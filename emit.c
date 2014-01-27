/*
 * Copyright 2011      Leiden University. All rights reserved.
 * Copyright 2013-2014 Ecole Normale Superieure. All rights reserved.
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

#include <yaml.h>

#include "expr.h"
#include "loc.h"
#include "scop.h"
#include "scop_yaml.h"
#include "tree.h"

static int emit_string(yaml_emitter_t *emitter, const char *str)
{
	yaml_event_t event;

	if (!yaml_scalar_event_initialize(&event, NULL, NULL,
				    (yaml_char_t *) str, strlen(str),
				    1, 1, YAML_PLAIN_SCALAR_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

/* Print the string "name" and the string "str" to "emitter".
 */
static int emit_named_string(yaml_emitter_t *emitter, const char *name,
	const char *str)
{
	if (emit_string(emitter, name) < 0)
		return -1;
	if (emit_string(emitter, str) < 0)
		return -1;
	return 0;
}

/* Print the isl_id "id" to "emitter".
 */
static int emit_id(yaml_emitter_t *emitter, __isl_keep isl_id *id)
{
	return emit_string(emitter, isl_id_get_name(id));
}

/* Print the string "name" and the isl_id "id" to "emitter".
 */
static int emit_named_id(yaml_emitter_t *emitter, const char *name,
	__isl_keep isl_id *id)
{
	if (emit_string(emitter, name) < 0)
		return -1;
	if (emit_id(emitter, id) < 0)
		return -1;
	return 0;
}

static int emit_int(yaml_emitter_t *emitter, int i)
{
	char buffer[40];

	snprintf(buffer, sizeof(buffer), "%d", i);
	return emit_string(emitter, buffer);
}

static int emit_named_int(yaml_emitter_t *emitter, const char *name, int i)
{
	if (emit_string(emitter, name) < 0)
		return -1;
	if (emit_int(emitter, i) < 0)
		return -1;
	return 0;
}

/* Print the unsigned integer "u" to "emitter".
 */
static int emit_unsigned(yaml_emitter_t *emitter, unsigned u)
{
	char buffer[40];

	snprintf(buffer, sizeof(buffer), "%u", u);
	return emit_string(emitter, buffer);
}

/* Print the string "name" and the unsigned integer "u" to "emitter".
 */
static int emit_named_unsigned(yaml_emitter_t *emitter, const char *name,
	unsigned u)
{
	if (emit_string(emitter, name) < 0)
		return -1;
	if (emit_int(emitter, u) < 0)
		return -1;
	return 0;
}

static int emit_double(yaml_emitter_t *emitter, double d)
{
	char buffer[40];

	snprintf(buffer, sizeof(buffer), "%g", d);
	return emit_string(emitter, buffer);
}

static int emit_map(yaml_emitter_t *emitter, __isl_keep isl_map *map)
{
	isl_ctx *ctx = isl_map_get_ctx(map);
	isl_printer *p;
	char *str;
	int r;

	p = isl_printer_to_str(ctx);
	p = isl_printer_print_map(p, map);
	str = isl_printer_get_str(p);
	isl_printer_free(p);
	r = emit_string(emitter, str);
	free(str);
	return r;
}

/* Print the isl_val "val" to "emitter".
 */
static int emit_val(yaml_emitter_t *emitter, __isl_keep isl_val *val)
{
	isl_ctx *ctx = isl_val_get_ctx(val);
	isl_printer *p;
	char *str;
	int r;

	p = isl_printer_to_str(ctx);
	p = isl_printer_print_val(p, val);
	str = isl_printer_get_str(p);
	isl_printer_free(p);
	r = emit_string(emitter, str);
	free(str);
	return r;
}

/* Print the string "name" and the isl_val "val" to "emitter".
 */
static int emit_named_val(yaml_emitter_t *emitter, const char *name,
	__isl_keep isl_val *val)
{
	if (emit_string(emitter, name) < 0)
		return -1;
	if (emit_val(emitter, val) < 0)
		return -1;
	return 0;
}

static int emit_set(yaml_emitter_t *emitter, __isl_keep isl_set *set)
{
	isl_ctx *ctx = isl_set_get_ctx(set);
	isl_printer *p;
	char *str;
	int r;

	p = isl_printer_to_str(ctx);
	p = isl_printer_print_set(p, set);
	str = isl_printer_get_str(p);
	isl_printer_free(p);
	r = emit_string(emitter, str);
	free(str);
	return r;
}

static int emit_named_set(yaml_emitter_t *emitter, const char *name,
	__isl_keep isl_set *set)
{
	if (emit_string(emitter, name) < 0)
		return -1;
	if (emit_set(emitter, set) < 0)
		return -1;
	return 0;
}

/* Print the string "name" and the map "map" to "emitter".
 */
static int emit_named_map(yaml_emitter_t *emitter, const char *name,
	__isl_keep isl_map *map)
{
	if (emit_string(emitter, name) < 0)
		return -1;
	if (emit_map(emitter, map) < 0)
		return -1;
	return 0;
}

/* Print the isl_multi_pw_aff "mpa" to "emitter".
 */
static int emit_multi_pw_aff(yaml_emitter_t *emitter,
	__isl_keep isl_multi_pw_aff *mpa)
{
	isl_ctx *ctx = isl_multi_pw_aff_get_ctx(mpa);
	isl_printer *p;
	char *str;
	int r;

	p = isl_printer_to_str(ctx);
	p = isl_printer_print_multi_pw_aff(p, mpa);
	str = isl_printer_get_str(p);
	isl_printer_free(p);
	r = emit_string(emitter, str);
	free(str);
	return r;
}

/* Print the string "name" and the isl_multi_pw_aff "mpa" to "emitter".
 */
static int emit_named_multi_pw_aff(yaml_emitter_t *emitter, const char *name,
	__isl_keep isl_multi_pw_aff *mpa)
{
	if (emit_string(emitter, name) < 0)
		return -1;
	if (emit_multi_pw_aff(emitter, mpa) < 0)
		return -1;
	return 0;
}

/* Print "type" to "emitter".
 */
static int emit_type(yaml_emitter_t *emitter, struct pet_type *type)
{
	yaml_event_t event;

	if (!yaml_mapping_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_MAPPING_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	if (emit_string(emitter, "name") < 0)
		return -1;
	if (emit_string(emitter, type->name) < 0)
		return -1;

	if (emit_string(emitter, "definition") < 0)
		return -1;
	if (emit_string(emitter, type->definition) < 0)
		return -1;

	if (!yaml_mapping_end_event_initialize(&event))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

/* Print the list of "n_type" "types", if any, to "emitter".
 */
static int emit_types(yaml_emitter_t *emitter, int n_type,
	struct pet_type **types)
{
	int i;
	yaml_event_t event;

	if (n_type == 0)
		return 0;

	if (emit_string(emitter, "types") < 0)
		return -1;
	if (!yaml_sequence_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_SEQUENCE_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	for (i = 0; i < n_type; ++i)
		if (emit_type(emitter, types[i]) < 0)
			return -1;

	if (!yaml_sequence_end_event_initialize(&event))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

static int emit_array(yaml_emitter_t *emitter, struct pet_array *array)
{
	yaml_event_t event;

	if (!yaml_mapping_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_MAPPING_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	if (emit_string(emitter, "context") < 0)
		return -1;
	if (emit_set(emitter, array->context) < 0)
		return -1;

	if (emit_string(emitter, "extent") < 0)
		return -1;
	if (emit_set(emitter, array->extent) < 0)
		return -1;

	if (array->value_bounds) {
		if (emit_string(emitter, "value_bounds") < 0)
			return -1;
		if (emit_set(emitter, array->value_bounds) < 0)
			return -1;
	}

	if (emit_string(emitter, "element_type") < 0)
		return -1;
	if (emit_string(emitter, array->element_type) < 0)
		return -1;
	if (emit_named_int(emitter, "element_size", array->element_size) < 0)
		return -1;

	if (array->element_is_record)
		if (emit_named_int(emitter, "element_is_record",
					array->element_is_record) < 0)
			return -1;

	if (array->live_out) {
		if (emit_string(emitter, "live_out") < 0)
			return -1;
		if (emit_string(emitter, "1") < 0)
			return -1;
	}

	if (array->uniquely_defined) {
		if (emit_string(emitter, "uniquely_defined") < 0)
			return -1;
		if (emit_string(emitter, "1") < 0)
			return -1;
	}

	if (array->declared && emit_named_int(emitter, "declared", 1) < 0)
		return -1;
	if (array->exposed && emit_named_int(emitter, "exposed", 1) < 0)
		return -1;

	if (!yaml_mapping_end_event_initialize(&event))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

static int emit_arrays(yaml_emitter_t *emitter, int n_array,
	struct pet_array **arrays)
{
	int i;
	yaml_event_t event;

	if (emit_string(emitter, "arrays") < 0)
		return -1;
	if (!yaml_sequence_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_SEQUENCE_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	for (i = 0; i < n_array; ++i)
		if (emit_array(emitter, arrays[i]) < 0)
			return -1;

	if (!yaml_sequence_end_event_initialize(&event))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

static int emit_expr_type(yaml_emitter_t *emitter, enum pet_expr_type type)
{
	if (emit_string(emitter, pet_type_str(type)) < 0)
		return -1;
	return 0;
}

static int emit_expr(yaml_emitter_t *emitter, __isl_keep pet_expr *expr)
{
	yaml_event_t event;

	if (!yaml_mapping_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_MAPPING_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	if (emit_string(emitter, "type") < 0)
		return -1;
	if (emit_expr_type(emitter, expr->type) < 0)
		return -1;

	switch (expr->type) {
	case pet_expr_error:
		return -1;
	case pet_expr_int:
		if (emit_named_val(emitter, "value", expr->i) < 0)
			return -1;
		break;
	case pet_expr_double:
		if (emit_string(emitter, "value") < 0)
			return -1;
		if (emit_double(emitter, expr->d.val) < 0)
			return -1;
		if (emit_string(emitter, "string") < 0)
			return -1;
		if (emit_string(emitter, expr->d.s) < 0)
			return -1;
		break;
	case pet_expr_access:
		if (emit_string(emitter, "relation") < 0)
			return -1;
		if (emit_map(emitter, expr->acc.access) < 0)
			return -1;
		if (emit_named_multi_pw_aff(emitter,
					    "index", expr->acc.index) < 0)
			return -1;
		if (expr->acc.ref_id &&
		    emit_named_id(emitter, "reference", expr->acc.ref_id) < 0)
			return -1;
		if (emit_string(emitter, "read") < 0)
			return -1;
		if (emit_int(emitter, expr->acc.read) < 0)
			return -1;
		if (emit_string(emitter, "write") < 0)
			return -1;
		if (emit_int(emitter, expr->acc.write) < 0)
			return -1;
		break;
	case pet_expr_op:
		if (emit_string(emitter, "operation") < 0)
			return -1;
		if (emit_string(emitter, pet_op_str(expr->op)) < 0)
			return -1;
		break;
	case pet_expr_call:
		if (emit_string(emitter, "name") < 0)
			return -1;
		if (emit_string(emitter, expr->name) < 0)
			return -1;
		break;
	case pet_expr_cast:
		if (emit_string(emitter, "type_name") < 0)
			return -1;
		if (emit_string(emitter, expr->type_name) < 0)
			return -1;
		break;
	}

	if (expr->n_arg > 0) {
		int i;

		if (emit_string(emitter, "arguments") < 0)
			return -1;
		if (!yaml_sequence_start_event_initialize(&event, NULL, NULL, 1,
						    YAML_BLOCK_SEQUENCE_STYLE))
			return -1;
		if (!yaml_emitter_emit(emitter, &event))
			return -1;

		for (i = 0; i < expr->n_arg; ++i)
			if (emit_expr(emitter, expr->args[i]) < 0)
				return -1;

		if (!yaml_sequence_end_event_initialize(&event))
			return -1;
		if (!yaml_emitter_emit(emitter, &event))
			return -1;
	}

	if (!yaml_mapping_end_event_initialize(&event))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

/* Print the string "name" and the expression "expr" to "emitter".
 */
static int emit_named_expr(yaml_emitter_t *emitter, const char *name,
	 __isl_keep pet_expr *expr)
{
	if (emit_string(emitter, name) < 0)
		return -1;
	if (emit_expr(emitter, expr) < 0)
		return -1;
	return 0;
}

/* Print "type" to "emitter".
 */
static int emit_tree_type(yaml_emitter_t *emitter, enum pet_tree_type type)
{
	if (emit_string(emitter, pet_tree_type_str(type)) < 0)
		return -1;
	return 0;
}

/* Recursively print "tree" to "emitter".
 */
static int emit_tree(yaml_emitter_t *emitter, __isl_keep pet_tree *tree)
{
	yaml_event_t event;
	int i;

	if (!yaml_mapping_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_MAPPING_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	if (emit_string(emitter, "type") < 0)
		return -1;
	if (emit_tree_type(emitter, tree->type) < 0)
		return -1;

	switch (tree->type) {
	case pet_tree_error:
		return -1;
	case pet_tree_block:
		if (emit_named_int(emitter, "block", tree->u.b.block) < 0)
			return -1;
		if (tree->u.b.n == 0)
			break;

		if (emit_string(emitter, "children") < 0)
			return -1;
		if (!yaml_sequence_start_event_initialize(&event, NULL, NULL, 1,
						    YAML_BLOCK_SEQUENCE_STYLE))
			return -1;
		if (!yaml_emitter_emit(emitter, &event))
			return -1;

		for (i = 0; i < tree->u.b.n; ++i)
			if (emit_tree(emitter, tree->u.b.child[i]) < 0)
				return -1;

		if (!yaml_sequence_end_event_initialize(&event))
			return -1;
		if (!yaml_emitter_emit(emitter, &event))
			return -1;
		break;
	case pet_tree_break:
	case pet_tree_continue:
		break;
	case pet_tree_decl:
		if (emit_named_expr(emitter, "variable", tree->u.d.var) < 0)
			return -1;
		break;
	case pet_tree_decl_init:
		if (emit_named_expr(emitter, "variable", tree->u.d.var) < 0)
			return -1;
		if (emit_named_expr(emitter,
				    "initialization", tree->u.d.init) < 0)
			return -1;
		break;
	case pet_tree_expr:
		if (emit_named_expr(emitter, "expr", tree->u.e.expr) < 0)
			return -1;
		break;
	case pet_tree_for:
		if (emit_named_int(emitter, "declared", tree->u.l.declared) < 0)
			return -1;
		if (emit_named_expr(emitter, "variable", tree->u.l.iv) < 0)
			return -1;
		if (emit_named_expr(emitter,
				    "initialization", tree->u.l.init) < 0)
			return -1;
		if (emit_named_expr(emitter, "condition", tree->u.l.cond) < 0)
			return -1;
		if (emit_named_expr(emitter, "increment", tree->u.l.inc) < 0)
			return -1;
		if (emit_string(emitter, "body") < 0)
			return -1;
		if (emit_tree(emitter, tree->u.l.body) < 0)
			return -1;
		break;
	case pet_tree_while:
		if (emit_named_expr(emitter, "condition", tree->u.l.cond) < 0)
			return -1;
		if (emit_string(emitter, "body") < 0)
			return -1;
		if (emit_tree(emitter, tree->u.l.body) < 0)
			return -1;
		break;
	case pet_tree_infinite_loop:
		if (emit_string(emitter, "body") < 0)
			return -1;
		if (emit_tree(emitter, tree->u.l.body) < 0)
			return -1;
		break;
	case pet_tree_if:
		if (emit_named_expr(emitter, "condition", tree->u.i.cond) < 0)
			return -1;
		if (emit_string(emitter, "then") < 0)
			return -1;
		if (emit_tree(emitter, tree->u.i.then_body) < 0)
			return -1;
		break;
	case pet_tree_if_else:
		if (emit_named_expr(emitter, "condition", tree->u.i.cond) < 0)
			return -1;
		if (emit_string(emitter, "then") < 0)
			return -1;
		if (emit_tree(emitter, tree->u.i.then_body) < 0)
			return -1;
		if (emit_string(emitter, "else") < 0)
			return -1;
		if (emit_tree(emitter, tree->u.i.else_body) < 0)
			return -1;
		break;
	}

	if (!yaml_mapping_end_event_initialize(&event))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

static int emit_stmt(yaml_emitter_t *emitter, struct pet_stmt *stmt)
{
	yaml_event_t event;

	if (!yaml_mapping_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_MAPPING_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	if (emit_string(emitter, "line") < 0)
		return -1;
	if (emit_int(emitter, pet_loc_get_line(stmt->loc)) < 0)
		return -1;

	if (emit_string(emitter, "domain") < 0)
		return -1;
	if (emit_set(emitter, stmt->domain) < 0)
		return -1;

	if (emit_string(emitter, "schedule") < 0)
		return -1;
	if (emit_map(emitter, stmt->schedule) < 0)
		return -1;

	if (emit_string(emitter, "body") < 0)
		return -1;
	if (emit_tree(emitter, stmt->body) < 0)
		return -1;

	if (stmt->n_arg > 0) {
		int i;

		if (emit_string(emitter, "arguments") < 0)
			return -1;
		if (!yaml_sequence_start_event_initialize(&event, NULL, NULL, 1,
						    YAML_BLOCK_SEQUENCE_STYLE))
			return -1;
		if (!yaml_emitter_emit(emitter, &event))
			return -1;

		for (i = 0; i < stmt->n_arg; ++i)
			if (emit_expr(emitter, stmt->args[i]) < 0)
				return -1;

		if (!yaml_sequence_end_event_initialize(&event))
			return -1;
		if (!yaml_emitter_emit(emitter, &event))
			return -1;
	}

	if (!yaml_mapping_end_event_initialize(&event))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

static int emit_statements(yaml_emitter_t *emitter, int n_stmt,
	struct pet_stmt **stmts)
{
	int i;
	yaml_event_t event;

	if (emit_string(emitter, "statements") < 0)
		return -1;
	if (!yaml_sequence_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_SEQUENCE_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	for (i = 0; i < n_stmt; ++i)
		if (emit_stmt(emitter, stmts[i]) < 0)
			return -1;

	if (!yaml_sequence_end_event_initialize(&event))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

/* Print "implication" to "emitter".
 */
static int emit_implication(yaml_emitter_t *emitter,
	struct pet_implication *implication)
{
	yaml_event_t event;

	if (!yaml_mapping_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_MAPPING_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	if (emit_named_int(emitter, "satisfied", implication->satisfied) < 0)
		return -1;

	if (emit_named_map(emitter, "extension", implication->extension) < 0)
		return -1;

	if (!yaml_mapping_end_event_initialize(&event))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

/* Print the list of "n_implication" "implications", if any, to "emitter".
 */
static int emit_implications(yaml_emitter_t *emitter, int n_implication,
	struct pet_implication **implications)
{
	int i;
	yaml_event_t event;

	if (n_implication == 0)
		return 0;

	if (emit_string(emitter, "implications") < 0)
		return -1;
	if (!yaml_sequence_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_SEQUENCE_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	for (i = 0; i < n_implication; ++i)
		if (emit_implication(emitter, implications[i]) < 0)
			return -1;

	if (!yaml_sequence_end_event_initialize(&event))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

static int emit_scop(yaml_emitter_t *emitter, struct pet_scop *scop)
{
	yaml_event_t event;

	if (!yaml_mapping_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_MAPPING_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	if (emit_named_unsigned(emitter,
				"start", pet_loc_get_start(scop->loc)) < 0)
		return -1;
	if (emit_named_unsigned(emitter, "end", pet_loc_get_end(scop->loc)) < 0)
		return -1;
	if (emit_named_string(emitter,
				"indent", pet_loc_get_indent(scop->loc)) < 0)
		return -1;
	if (emit_string(emitter, "context") < 0)
		return -1;
	if (emit_set(emitter, scop->context) < 0)
		return -1;
	if (!isl_set_plain_is_universe(scop->context_value) &&
	    emit_named_set(emitter, "context_value", scop->context_value) < 0)
		return -1;

	if (emit_types(emitter, scop->n_type, scop->types) < 0)
		return -1;
	if (emit_arrays(emitter, scop->n_array, scop->arrays) < 0)
		return -1;

	if (emit_statements(emitter, scop->n_stmt, scop->stmts) < 0)
		return -1;

	if (emit_implications(emitter, scop->n_implication,
				scop->implications) < 0)
		return -1;

	if (!yaml_mapping_end_event_initialize(&event))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	return 0;
}

/* Print a YAML serialization of "scop" to "out".
 */
int pet_scop_emit(FILE *out, struct pet_scop *scop)
{
	yaml_emitter_t emitter;
	yaml_event_t event;

	yaml_emitter_initialize(&emitter);

	yaml_emitter_set_output_file(&emitter, out);

	yaml_stream_start_event_initialize(&event, YAML_UTF8_ENCODING);
	if (!yaml_emitter_emit(&emitter, &event))
		goto error;

	if (!yaml_document_start_event_initialize(&event, NULL, NULL, NULL, 1))
		goto error;
	if (!yaml_emitter_emit(&emitter, &event))
		goto error;

	if (emit_scop(&emitter, scop) < 0)
		goto error;

	if (!yaml_document_end_event_initialize(&event, 1))
		goto error;
	if (!yaml_emitter_emit(&emitter, &event))
		goto error;

	yaml_stream_end_event_initialize(&event);
	if (!yaml_emitter_emit(&emitter, &event))
		goto error;

	yaml_emitter_delete(&emitter);
	return 0;
error:
	yaml_emitter_delete(&emitter);
	return -1;
}
