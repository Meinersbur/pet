/*
 * Copyright 2011 Leiden University. All rights reserved.
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

static int extract_double(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return -1);

	return strtod((char *) node->data.scalar.value, NULL);
}

static enum pet_expr_type extract_type(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
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

static __isl_give isl_map *extract_map(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	if (node->type != YAML_SCALAR_NODE)
		isl_die(ctx, isl_error_invalid, "expecting scalar node",
			return NULL);

	return isl_map_read_from_str(ctx, (char *) node->data.scalar.value);
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
		if (!strcmp((char *) key->data.scalar.value, "live_out"))
			array->live_out = extract_int(ctx, document, value);
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

static struct pet_expr *extract_expr(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node);

static struct pet_expr *extract_arguments(isl_ctx *ctx,
	yaml_document_t *document, yaml_node_t *node, struct pet_expr *expr)
{
	int i;
	yaml_node_item_t *item;

	if (node->type != YAML_SEQUENCE_NODE)
		isl_die(ctx, isl_error_invalid, "expecting sequence",
			return pet_expr_free(expr));

	expr->n_arg = node->data.sequence.items.top
				- node->data.sequence.items.start;
	expr->args = isl_calloc_array(ctx, struct pet_expr *, expr->n_arg);
	if (!expr->args)
		return pet_expr_free(expr);

	for (item = node->data.sequence.items.start, i = 0;
	     item < node->data.sequence.items.top; ++item, ++i) {
		yaml_node_t *n;

		n = yaml_document_get_node(document, *item);
		expr->args[i] = extract_expr(ctx, document, n);
		if (!expr->args[i])
			return pet_expr_free(expr);
	}

	return expr;
}

static struct pet_expr *extract_expr(isl_ctx *ctx, yaml_document_t *document,
	yaml_node_t *node)
{
	struct pet_expr *expr;
	yaml_node_pair_t * pair;

	if (node->type != YAML_MAPPING_NODE)
		isl_die(ctx, isl_error_invalid, "expecting mapping",
			return NULL);

	expr = isl_calloc_type(ctx, struct pet_expr);
	if (!expr)
		return NULL;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_expr_free(expr));

		if (!strcmp((char *) key->data.scalar.value, "type"))
			expr->type = extract_type(ctx, document, value);

		if (!strcmp((char *) key->data.scalar.value, "value"))
			expr->d = extract_double(ctx, document, value);

		if (!strcmp((char *) key->data.scalar.value, "relation"))
			expr->acc.access = extract_map(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "read"))
			expr->acc.read = extract_int(ctx, document, value);
		if (!strcmp((char *) key->data.scalar.value, "write"))
			expr->acc.write = extract_int(ctx, document, value);

		if (!strcmp((char *) key->data.scalar.value, "operation"))
			expr->op = extract_op(ctx, document, value);

		if (!strcmp((char *) key->data.scalar.value, "name"))
			expr->name = extract_string(ctx, document, value);

		if (!strcmp((char *) key->data.scalar.value, "arguments"))
			expr = extract_arguments(ctx, document, value, expr);
		if (!expr)
			return NULL;
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
	stmt->args = isl_calloc_array(ctx, struct pet_expr *, stmt->n_arg);
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

	if (node->type != YAML_MAPPING_NODE)
		isl_die(ctx, isl_error_invalid, "expecting mapping",
			return NULL);

	stmt = isl_calloc_type(ctx, struct pet_stmt);
	if (!stmt)
		return NULL;

	for (pair = node->data.mapping.pairs.start;
	     pair < node->data.mapping.pairs.top; ++pair) {
		yaml_node_t *key, *value;

		key = yaml_document_get_node(document, pair->key);
		value = yaml_document_get_node(document, pair->value);

		if (key->type != YAML_SCALAR_NODE)
			isl_die(ctx, isl_error_invalid, "expecting scalar key",
				return pet_stmt_free(stmt));

		if (!strcmp((char *) key->data.scalar.value, "line"))
			stmt->line = extract_int(ctx, document, value);
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

	scop = isl_calloc_type(ctx, struct pet_scop);
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
		if (!strcmp((char *) key->data.scalar.value, "arrays"))
			scop = extract_arrays(ctx, document, value, scop);
		if (!strcmp((char *) key->data.scalar.value, "statements"))
			scop = extract_statements(ctx, document, value, scop);
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
