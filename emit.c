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

#include <yaml.h>

#include "scop.h"
#include "scop_yaml.h"

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

static int emit_int(yaml_emitter_t *emitter, int i)
{
	char buffer[40];

	snprintf(buffer, sizeof(buffer), "%d", i);
	return emit_string(emitter, buffer);
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

	if (array->live_out) {
		if (emit_string(emitter, "live_out") < 0)
			return -1;
		if (emit_string(emitter, "1") < 0)
			return -1;
	}

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

static int emit_type(yaml_emitter_t *emitter, enum pet_expr_type type)
{
	if (emit_string(emitter, pet_type_str(type)) < 0)
		return -1;
	return 0;
}

static int emit_expr(yaml_emitter_t *emitter, struct pet_expr *expr)
{
	yaml_event_t event;

	if (!yaml_mapping_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_MAPPING_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	if (emit_string(emitter, "type") < 0)
		return -1;
	if (emit_type(emitter, expr->type) < 0)
		return -1;

	switch (expr->type) {
	case pet_expr_double:
		if (emit_string(emitter, "value") < 0)
			return -1;
		if (emit_double(emitter, expr->d) < 0)
			return -1;
		break;
	case pet_expr_access:
		if (emit_string(emitter, "relation") < 0)
			return -1;
		if (emit_map(emitter, expr->acc.access) < 0)
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
	case pet_expr_unary:
	case pet_expr_binary:
		if (emit_string(emitter, "operation") < 0)
			return -1;
		if (emit_string(emitter, pet_op_str(expr->op)) < 0)
			return -1;
		break;
	case pet_expr_ternary:
		break;
	case pet_expr_call:
		if (emit_string(emitter, "name") < 0)
			return -1;
		if (emit_string(emitter, expr->name) < 0)
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
	if (emit_int(emitter, stmt->line) < 0)
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
	if (emit_expr(emitter, stmt->body) < 0)
		return -1;

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

static int emit_scop(yaml_emitter_t *emitter, struct pet_scop *scop)
{
	yaml_event_t event;

	if (!yaml_mapping_start_event_initialize(&event, NULL, NULL, 1,
						YAML_BLOCK_MAPPING_STYLE))
		return -1;
	if (!yaml_emitter_emit(emitter, &event))
		return -1;

	if (emit_string(emitter, "context") < 0)
		return -1;
	if (emit_set(emitter, scop->context) < 0)
		return -1;
	if (!isl_set_plain_is_universe(scop->context_value) &&
	    emit_named_set(emitter, "context_value", scop->context_value) < 0)
		return -1;

	if (emit_arrays(emitter, scop->n_array, scop->arrays) < 0)
		return -1;

	if (emit_statements(emitter, scop->n_stmt, scop->stmts) < 0)
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
