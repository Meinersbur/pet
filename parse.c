/*
 * Copyright 2011 Leiden University. All rights reserved.
 * Copyright 2013 Ecole Normale Superieure. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 
 *    1. Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 * 
 *    2. Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY LEIDEN UNIVERSITY ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL LEIDEN UNIVERSITY OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * The views and conclusions contained in the software and documentation
 * are those of the authors and should not be interpreted as
 * representing official policies, either expressed or implied, of
 * Leiden University.
 */ 

#include <stdlib.h>
#include <yaml.h>

#include "expr.h"
#include "loc.h"
#include "scop.h"
#include "scop_yaml.h"

static char *extract_string(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return NULL);

	return strdup((char *) node->data.scalar.value);
}

static int extract_int(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return -1);

	return atoi((char *) node->data.scalar.value);
}

static double extract_double(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return -1);

	return strtod((char *) node->data.scalar.value, NULL);
}

static enum pet_expr_type extract_expr_type(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return -1);

	return pet_str_type((char *) node->data.scalar.value);
}

static enum pet_op_type extract_op(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return -1);

	return pet_str_op((char *) node->data.scalar.value);
}

static __isl_give isl_set *extract_set(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return NULL);

	return isl_set_read_from_str(ctx, (char *) node->data.scalar.value);
}

static __isl_give isl_id *extract_id(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return NULL);

	return isl_id_alloc(ctx, (char *) node->data.scalar.value, NULL);
}

static __isl_give isl_map *extract_map(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return NULL);

	return isl_map_read_from_str(ctx, (char *) node->data.scalar.value);
}

/* Extract an isl_val from "node".
 */
static __isl_give isl_val *extract_val(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return NULL);

	return isl_val_read_from_str(ctx, (char *) node->data.scalar.value);
}

/* Extract an isl_multi_pw_aff from "node".
 */
static __isl_give isl_multi_pw_aff *extract_multi_pw_aff(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return NULL);

	return isl_multi_pw_aff_read_from_str(ctx,
					    (char *) node->data.scalar.value);
}

/* Extract a pet_type from "node".
 */
static struct pet_type *extract_type(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node)
{
	struct pet_type *type;
	yaml_node_pair_t * pair;

	if (node->type != YAML_MAPPING_NODE)
		isl_die(ctx, isl_error_invalid, "expecting mapping",
			return NULL);

	type = isl_calloc_type(ctx, struct pet_type);
	if (!type)
		return NULL;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_type_free(type));

		if (!strcmp((char *) key->data.scalar.value, "name"))
			type->name = extract_string(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "definition"))
			type->definition = extract_string(ctx, document, value);
	}

	return type;
}

/* Extract a sequence of types from "node" and store them in scop->types.
 */
static struct pet_scop *extract_types(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, struct pet_scop *scop)
{
	int i;
	yaml_node_item_t *item;

	if (node->type != YAML_SEQUENCE_NODE)
		isl_die(ctx, isl_error_invalid, "expecting sequence",
			return NULL);

	scop->n_type = node->data.sequence.items.top
				- node->data.sequence.items.start;
	scop->types = isl_calloc_array(ctx, struct pet_type *, scop->n_type);
	if (!scop->types)
		return pet_scop_free(scop);

	for (item = node->data.sequence.items.start, i = 0;
	     item < node->data.sequence.items.top; ++item, ++i) {
		yaml_node_t *n;

		n = yaml_document_get_node(document, *item);
		scop->types[i] = extract_type(ctx, document, n);
		if (!scop->types[i])
			return pet_scop_free(scop);
	}

	return scop;
}

static struct pet_array *extract_array(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	struct pet_array *array;
	yaml_node_pair_t * pair;

	if (node->type != YAML_MAPPING_NODE)
		isl_die(ctx, isl_error_invalid, "expecting mapping",
			return NULL);

	array = isl_calloc_type(ctx, struct pet_array);
	if (!array)
		return NULL;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_array_free(array));

		if (!strcmp((char *) key->data.scalar.value, "context"))
			array->context = extract_set(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "extent"))
			array->extent = extract_set(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "value_bounds"))
			array->value_bounds = extract_set(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "element_type"))
			array->element_type =
					extract_string(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "element_size"))
			array->element_size = extract_int(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value,
				"element_is_record"))
			array->element_is_record =
					extract_int(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "live_out"))
			array->live_out = extract_int(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value,
				"uniquely_defined"))
			array->uniquely_defined =
					extract_int(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "declared"))
			array->declared = extract_int(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "exposed"))
			array->exposed = extract_int(ctx, document, value);
	}

	return array;
}

static struct pet_scop *extract_arrays(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node, struct pet_scop *scop)
{
	int i;
	yaml_node_item_t *item;

	if (node->type != YAML_SEQUENCE_NODE)
		isl_die(ctx, isl_error_invalid, "expecting sequence",
			return NULL);

	scop->n_array = node->data.sequence.items.top
				- node->data.sequence.items.start;
	scop->arrays = isl_calloc_array(ctx, struct pet_array *, scop->n_array);
	if (!scop->arrays)
		return pet_scop_free(scop);

	for (item = node->data.sequence.items.start, i = 0;
	     item < node->data.sequence.items.top; ++item, ++i) {
		yaml_node_t *n;

		n = yaml_document_get_node(document, *item);
		scop->arrays[i] = extract_array(ctx, document, n);
		if (!scop->arrays[i])
			return pet_scop_free(scop);
	}

	return scop;
}

static __isl_give pet_expr *extract_expr(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node);

static __isl_give pet_expr *extract_arguments(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, __isl_take pet_expr *expr)
{
	int i, n;
	yaml_node_item_t *item;

	if (node->type != YAML_SEQUENCE_NODE)
		isl_die(ctx, isl_error_invalid, "expecting sequence",
			return pet_expr_free(expr));

	n = node->data.sequence.items.top - node->data.sequence.items.start;
	expr = pet_expr_set_n_arg(expr, n);

	for (item = node->data.sequence.items.start, i = 0;
	     item < node->data.sequence.items.top; ++item, ++i) {
		yaml_node_t *n;
		pet_expr *arg;

		n = yaml_document_get_node(document, *item);
		arg = extract_expr(ctx, document, n);
		expr = pet_expr_set_arg(expr, i, arg);
	}

	return expr;
}

/* Extract pet_expr_double specific fields from "node" and
 * update "expr" accordingly.
 */
static __isl_give pet_expr *extract_expr_double(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, __isl_take pet_expr *expr)
{
	yaml_node_pair_t *pair;
	double d = 0;
	char *s = NULL;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_expr_free(expr));

		if (!strcmp((char *) key->data.scalar.value, "value"))
			d = extract_double(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "string"))
			s = extract_string(ctx, document, value);
	}

	expr = pet_expr_double_set(expr, d, s);
	free(s);

	return expr;
}

/* Extract pet_expr_access specific fields from "node" and
 * update "expr" accordingly.
 */
static __isl_give pet_expr *extract_expr_access(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, __isl_take pet_expr *expr)
{
	yaml_node_pair_t *pair;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_expr_free(expr));

		if (!strcmp((char *) key->data.scalar.value, "relation"))
			expr = pet_expr_access_set_access(expr,
				    extract_map(ctx, document, value));
		if (!strcmp((char *) key->data.scalar.value, "index"))
			expr = pet_expr_access_set_index(expr,
				    extract_multi_pw_aff(ctx, document, value));
		if (!strcmp((char *) key->data.scalar.value, "reference"))
			expr = pet_expr_access_set_ref_id(expr,
				    extract_id(ctx, document, value));
		if (!strcmp((char *) key->data.scalar.value, "read"))
			expr = pet_expr_access_set_read(expr,
				    extract_int(ctx, document, value));
		if (!strcmp((char *) key->data.scalar.value, "write"))
			expr = pet_expr_access_set_write(expr,
				    extract_int(ctx, document, value));
	}

	return expr;
}

/* Extract operation expression specific fields from "node" and
 * update "expr" accordingly.
 */
static __isl_give pet_expr *extract_expr_op(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, __isl_take pet_expr *expr)
{
	yaml_node_pair_t *pair;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_expr_free(expr));

		if (!strcmp((char *) key->data.scalar.value, "operation"))
			expr = pet_expr_op_set_type(expr,
					    extract_op(ctx, document, value));
	}

	return expr;
}

/* Extract pet_expr_call specific fields from "node" and
 * update "expr" accordingly.
 */
static __isl_give pet_expr *extract_expr_call(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, __isl_take pet_expr *expr)
{
	yaml_node_pair_t *pair;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_expr_free(expr));

		if (!strcmp((char *) key->data.scalar.value, "name"))
			expr = pet_expr_call_set_name(expr,
					extract_string(ctx, document, value));
	}

	return expr;
}

/* Extract pet_expr_cast specific fields from "node" and
 * update "expr" accordingly.
 */
static __isl_give pet_expr *extract_expr_cast(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, __isl_take pet_expr *expr)
{
	yaml_node_pair_t *pair;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_expr_free(expr));

		if (!strcmp((char *) key->data.scalar.value, "type_name"))
			expr = pet_expr_cast_set_type_name(expr,
					extract_string(ctx, document, value));
	}

	return expr;
}

/* Extract pet_expr_int specific fields from "node" and
 * update "expr" accordingly.
 */
static __isl_give pet_expr *extract_expr_int(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, __isl_take pet_expr *expr)
{
	yaml_node_pair_t * pair;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_expr_free(expr));

		if (!strcmp((char *) key->data.scalar.value, "value"))
			expr = pet_expr_int_set_val(expr,
					    extract_val(ctx, document, value));
	}

	return expr;
}

/* Extract a pet_expr from "node".
 *
 * We first extract the type and arguments of the expression and
 * then extract additional fields depending on the type.
 */
static __isl_give pet_expr *extract_expr(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node)
{
	enum pet_expr_type type = pet_expr_error;
	pet_expr *expr;
	yaml_node_pair_t *pair;

	if (node->type != YAML_MAPPING_NODE)
		isl_die(ctx, isl_error_invalid, "expecting mapping",
			return NULL);

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_expr_free(expr));

		if (!strcmp((char *) key->data.scalar.value, "type"))
			type = extract_expr_type(ctx, document, value);
	}

	if (type == pet_expr_error)
		isl_die(ctx, isl_error_invalid, "cannot determine type",
			return NULL);

	expr = pet_expr_alloc(ctx, type);
	if (!expr)
		return NULL;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (!strcmp((char *) key->data.scalar.value, "arguments"))
			expr = extract_arguments(ctx, document, value, expr);
		if (!expr)
			return NULL;
	}

	switch (type) {
	case pet_expr_error:
		isl_die(ctx, isl_error_internal, "unreachable code",
			return NULL);
	case pet_expr_access:
		expr = extract_expr_access(ctx, document, node, expr);
		break;
	case pet_expr_double:
		expr = extract_expr_double(ctx, document, node, expr);
		break;
	case pet_expr_call:
		expr = extract_expr_call(ctx, document, node, expr);
		break;
	case pet_expr_cast:
		expr = extract_expr_cast(ctx, document, node, expr);
		break;
	case pet_expr_int:
		expr = extract_expr_int(ctx, document, node, expr);
		break;
	case pet_expr_op:
		expr = extract_expr_op(ctx, document, node, expr);
		break;
	}

	return expr;
}

static struct pet_stmt *extract_stmt_arguments(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, struct pet_stmt *stmt)
{
	int i;
	yaml_node_item_t *item;

	if (node->type != YAML_SEQUENCE_NODE)
		isl_die(ctx, isl_error_invalid, "expecting sequence",
			return pet_stmt_free(stmt));

	stmt->n_arg = node->data.sequence.items.top
				- node->data.sequence.items.start;
	stmt->args = isl_calloc_array(ctx, pet_expr *, stmt->n_arg);
	if (!stmt->args)
		return pet_stmt_free(stmt);

	for (item = node->data.sequence.items.start, i = 0;
	     item < node->data.sequence.items.top; ++item, ++i) {
		yaml_node_t *n;

		n = yaml_document_get_node(document, *item);
		stmt->args[i] = extract_expr(ctx, document, n);
		if (!stmt->args[i])
			return pet_stmt_free(stmt);
	}

	return stmt;
}

static struct pet_stmt *extract_stmt(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	struct pet_stmt *stmt;
	yaml_node_pair_t * pair;
	int line = -1;
	unsigned start = 0, end = 0;
	char *indent = NULL;

	if (node->type != YAML_MAPPING_NODE)
		isl_die(ctx, isl_error_invalid, "expecting mapping",
			return NULL);

	stmt = isl_calloc_type(ctx, struct pet_stmt);
	if (!stmt)
		return NULL;

	stmt->loc = &pet_loc_dummy;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_stmt_free(stmt));

		if (!strcmp((char *) key->data.scalar.value, "indent"))
			indent = extract_string(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "line"))
			line = extract_int(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "start"))
			start = extract_int(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "end"))
			end = extract_int(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "domain"))
			stmt->domain = extract_set(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "schedule"))
			stmt->schedule = extract_map(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "body"))
			stmt->body = extract_expr(ctx, document, value);

		if (!strcmp((char *) key->data.scalar.value, "arguments"))
			stmt = extract_stmt_arguments(ctx, document,
							value, stmt);
		if (!stmt)
			return NULL;
	}

	if (!indent)
		indent = strdup("");
	stmt->loc = pet_loc_alloc(ctx, start, end, line, indent);
	if (!stmt->loc)
		return pet_stmt_free(stmt);

	return stmt;
}

static struct pet_scop *extract_statements(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, struct pet_scop *scop)
{
	int i;
	yaml_node_item_t *item;

	if (node->type != YAML_SEQUENCE_NODE)
		isl_die(ctx, isl_error_invalid, "expecting sequence",
			return NULL);

	scop->n_stmt = node->data.sequence.items.top
				- node->data.sequence.items.start;
	scop->stmts = isl_calloc_array(ctx, struct pet_stmt *, scop->n_stmt);
	if (!scop->stmts)
		return pet_scop_free(scop);

	for (item = node->data.sequence.items.start, i = 0;
	     item < node->data.sequence.items.top; ++item, ++i) {
		yaml_node_t *n;

		n = yaml_document_get_node(document, *item);
		scop->stmts[i] = extract_stmt(ctx, document, n);
		if (!scop->stmts[i])
			return pet_scop_free(scop);
	}

	return scop;
}

/* Extract a pet_implication from "node".
 */
static struct pet_implication *extract_implication(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node)
{
	struct pet_implication *implication;
	yaml_node_pair_t * pair;

	if (node->type != YAML_MAPPING_NODE)
		isl_die(ctx, isl_error_invalid, "expecting mapping",
			return NULL);

	implication = isl_calloc_type(ctx, struct pet_implication);
	if (!implication)
		return NULL;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_implication_free(implication));

		if (!strcmp((char *) key->data.scalar.value, "satisfied"))
			implication->satisfied =
					    extract_int(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "extension"))
			implication->extension =
					    extract_map(ctx, document, value);
	}

	return implication;
}

/* Extract a sequence of implications from "node" and
 * store them in scop->implications.
 */
static struct pet_scop *extract_implications(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, struct pet_scop *scop)
{
	int i;
	yaml_node_item_t *item;

	if (node->type != YAML_SEQUENCE_NODE)
		isl_die(ctx, isl_error_invalid, "expecting sequence",
			return NULL);

	scop->n_implication = node->data.sequence.items.top
				- node->data.sequence.items.start;
	scop->implications = isl_calloc_array(ctx, struct pet_implication *,
						scop->n_implication);
	if (!scop->implications)
		return pet_scop_free(scop);

	for (item = node->data.sequence.items.start, i = 0;
	     item < node->data.sequence.items.top; ++item, ++i) {
		yaml_node_t *n;

		n = yaml_document_get_node(document, *item);
		scop->implications[i] = extract_implication(ctx, document, n);
		if (!scop->implications[i])
			return pet_scop_free(scop);
	}

	return scop;
}

static struct pet_scop *extract_scop(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	struct pet_scop *scop;
	yaml_node_pair_t * pair;

	if (!node)
		return NULL;

	if (node->type != YAML_MAPPING_NODE)
		isl_die(ctx, isl_error_invalid, "expecting mapping",
			return NULL);

	scop = pet_scop_alloc(ctx);
	if (!scop)
		return NULL;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_scop_free(scop));
		if (!strcmp((char *) key->data.scalar.value, "context"))
			scop->context = extract_set(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "context_value"))
			scop->context_value = extract_set(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "types"))
			scop = extract_types(ctx, document, value, scop);
		if (!strcmp((char *) key->data.scalar.value, "arrays"))
			scop = extract_arrays(ctx, document, value, scop);
		if (!strcmp((char *) key->data.scalar.value, "statements"))
			scop = extract_statements(ctx, document, value, scop);
		if (!strcmp((char *) key->data.scalar.value, "implications"))
			scop = extract_implications(ctx, document, value, scop);
		if (!scop)
			return NULL;
	}

	if (!scop->context_value) {
		isl_space *space = isl_space_params_alloc(ctx, 0);
		scop->context_value = isl_set_universe(space);
		if (!scop->context_value)
			return pet_scop_free(scop);
	}

	return scop;
}

/* Extract a pet_scop from the YAML description in "in".
 */
struct pet_scop *pet_scop_parse(isl_ctx *ctx, FILE *in)
{
	struct pet_scop *scop = NULL;
	yaml_parser_t parser;
	yaml_node_t *root;
	yaml_document_t document = { 0 };

	yaml_parser_initialize(&parser);

	yaml_parser_set_input_file(&parser, in);

	if (!yaml_parser_load(&parser, &document))
		goto error;

	root = yaml_document_get_root_node(&document);

	scop = extract_scop(ctx, &document, root);

	yaml_document_delete(&document);

	yaml_parser_delete(&parser);

	return scop;
error:
	yaml_parser_delete(&parser);
	pet_scop_free(scop);
	return NULL;
}
