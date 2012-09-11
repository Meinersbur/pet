/*
 * Copyright 2011 Leiden University. All rights reserved.
 * Copyright 2012 Ecole Normale Superieure. All rights reserved.
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

#include <isl/constraint.h>
#include <isl/union_set.h>

#include "scop.h"

#define ARRAY_SIZE(array) (sizeof(array)/sizeof(*array))

static char *type_str[] = {
	[pet_expr_access] = "access",
	[pet_expr_call] = "call",
	[pet_expr_double] = "double",
	[pet_expr_unary] = "unary",
	[pet_expr_binary] = "binary",
	[pet_expr_ternary] = "ternary"
};

static char *op_str[] = {
	[pet_op_add_assign] = "+=",
	[pet_op_sub_assign] = "-=",
	[pet_op_mul_assign] = "*=",
	[pet_op_div_assign] = "/=",
	[pet_op_assign] = "=",
	[pet_op_add] = "+",
	[pet_op_sub] = "-",
	[pet_op_mul] = "*",
	[pet_op_div] = "/",
	[pet_op_mod] = "%",
	[pet_op_eq] = "==",
	[pet_op_le] = "<=",
	[pet_op_lt] = "<",
	[pet_op_gt] = ">",
	[pet_op_minus] = "-",
	[pet_op_post_inc] = "++",
	[pet_op_post_dec] = "--",
	[pet_op_pre_inc] = "++",
	[pet_op_pre_dec] = "--",
	[pet_op_address_of] = "&"
};

/* pet_scop with extra information that is only used during parsing.
 *
 * In particular, we keep track of conditions under which we want
 * to skip the rest of the current loop iteration (skip[pet_skip_now])
 * and of conditions under which we want to skip subsequent
 * loop iterations (skip[pet_skip_later]).
 *
 * The conditions are represented either by a variable, which
 * is assumed to attain values zero and one, or by a boolean affine
 * expression.  The condition holds if the variable has value one
 * or if the affine expression has value one (typically for only
 * part of the parameter space).
 *
 * A missing condition (skip[type] == NULL) means that we don't want
 * to skip anything.
 */
struct pet_scop_ext {
	struct pet_scop scop;

	isl_set *skip[2];
};

const char *pet_op_str(enum pet_op_type op)
{
	return op_str[op];
}

int pet_op_is_inc_dec(enum pet_op_type op)
{
	return op == pet_op_post_inc || op == pet_op_post_dec ||
	    op == pet_op_pre_inc || op == pet_op_pre_dec;
}

const char *pet_type_str(enum pet_expr_type type)
{
	return type_str[type];
}

enum pet_op_type pet_str_op(const char *str)
{
	int i;

	for (i = 0; i < ARRAY_SIZE(op_str); ++i)
		if (!strcmp(op_str[i], str))
			return i;

	return -1;
}

enum pet_expr_type pet_str_type(const char *str)
{
	int i;

	for (i = 0; i < ARRAY_SIZE(type_str); ++i)
		if (!strcmp(type_str[i], str))
			return i;

	return -1;
}

/* Construct a pet_expr from an access relation.
 * By default, it is considered to be a read access.
 */
struct pet_expr *pet_expr_from_access(__isl_take isl_map *access)
{
	isl_ctx *ctx = isl_map_get_ctx(access);
	struct pet_expr *expr;

	if (!access)
		return NULL;
	expr = isl_calloc_type(ctx, struct pet_expr);
	if (!expr)
		goto error;

	expr->type = pet_expr_access;
	expr->acc.access = access;
	expr->acc.read = 1;
	expr->acc.write = 0;

	return expr;
error:
	isl_map_free(access);
	return NULL;
}

/* Construct a unary pet_expr that performs "op" on "arg".
 */
struct pet_expr *pet_expr_new_unary(isl_ctx *ctx, enum pet_op_type op,
	struct pet_expr *arg)
{
	struct pet_expr *expr;

	if (!arg)
		goto error;
	expr = isl_alloc_type(ctx, struct pet_expr);
	if (!expr)
		goto error;

	expr->type = pet_expr_unary;
	expr->op = op;
	expr->n_arg = 1;
	expr->args = isl_calloc_array(ctx, struct pet_expr *, 1);
	if (!expr->args)
		goto error;
	expr->args[pet_un_arg] = arg;

	return expr;
error:
	pet_expr_free(arg);
	return NULL;
}

/* Construct a binary pet_expr that performs "op" on "lhs" and "rhs".
 */
struct pet_expr *pet_expr_new_binary(isl_ctx *ctx, enum pet_op_type op,
	struct pet_expr *lhs, struct pet_expr *rhs)
{
	struct pet_expr *expr;

	if (!lhs || !rhs)
		goto error;
	expr = isl_alloc_type(ctx, struct pet_expr);
	if (!expr)
		goto error;

	expr->type = pet_expr_binary;
	expr->op = op;
	expr->n_arg = 2;
	expr->args = isl_calloc_array(ctx, struct pet_expr *, 2);
	if (!expr->args)
		goto error;
	expr->args[pet_bin_lhs] = lhs;
	expr->args[pet_bin_rhs] = rhs;

	return expr;
error:
	pet_expr_free(lhs);
	pet_expr_free(rhs);
	return NULL;
}

/* Construct a ternary pet_expr that performs "cond" ? "lhs" : "rhs".
 */
struct pet_expr *pet_expr_new_ternary(isl_ctx *ctx, struct pet_expr *cond,
	struct pet_expr *lhs, struct pet_expr *rhs)
{
	struct pet_expr *expr;

	if (!cond || !lhs || !rhs)
		goto error;
	expr = isl_alloc_type(ctx, struct pet_expr);
	if (!expr)
		goto error;

	expr->type = pet_expr_ternary;
	expr->n_arg = 3;
	expr->args = isl_calloc_array(ctx, struct pet_expr *, 3);
	if (!expr->args)
		goto error;
	expr->args[pet_ter_cond] = cond;
	expr->args[pet_ter_true] = lhs;
	expr->args[pet_ter_false] = rhs;

	return expr;
error:
	pet_expr_free(cond);
	pet_expr_free(lhs);
	pet_expr_free(rhs);
	return NULL;
}

/* Construct a call pet_expr that calls function "name" with "n_arg"
 * arguments.  The caller is responsible for filling in the arguments.
 */
struct pet_expr *pet_expr_new_call(isl_ctx *ctx, const char *name,
	unsigned n_arg)
{
	struct pet_expr *expr;

	expr = isl_alloc_type(ctx, struct pet_expr);
	if (!expr)
		return NULL;

	expr->type = pet_expr_call;
	expr->n_arg = n_arg;
	expr->name = strdup(name);
	expr->args = isl_calloc_array(ctx, struct pet_expr *, n_arg);
	if (!expr->name || !expr->args)
		return pet_expr_free(expr);

	return expr;
}

/* Construct a pet_expr that represents the double "d".
 */
struct pet_expr *pet_expr_new_double(isl_ctx *ctx, double d)
{
	struct pet_expr *expr;

	expr = isl_calloc_type(ctx, struct pet_expr);
	if (!expr)
		return NULL;

	expr->type = pet_expr_double;
	expr->d = d;

	return expr;
}

void *pet_expr_free(struct pet_expr *expr)
{
	int i;

	if (!expr)
		return NULL;

	for (i = 0; i < expr->n_arg; ++i)
		pet_expr_free(expr->args[i]);
	free(expr->args);

	switch (expr->type) {
	case pet_expr_access:
		isl_map_free(expr->acc.access);
		break;
	case pet_expr_call:
		free(expr->name);
		break;
	case pet_expr_double:
	case pet_expr_unary:
	case pet_expr_binary:
	case pet_expr_ternary:
		break;
	}

	free(expr);
	return NULL;
}

static void expr_dump(struct pet_expr *expr, int indent)
{
	int i;

	if (!expr)
		return;

	fprintf(stderr, "%*s", indent, "");

	switch (expr->type) {
	case pet_expr_double:
		fprintf(stderr, "%g\n", expr->d);
		break;
	case pet_expr_access:
		isl_map_dump(expr->acc.access);
		fprintf(stderr, "%*sread: %d\n", indent + 2,
				"", expr->acc.read);
		fprintf(stderr, "%*swrite: %d\n", indent + 2,
				"", expr->acc.write);
		for (i = 0; i < expr->n_arg; ++i)
			expr_dump(expr->args[i], indent + 2);
		break;
	case pet_expr_unary:
		fprintf(stderr, "%s\n", op_str[expr->op]);
		expr_dump(expr->args[pet_un_arg], indent + 2);
		break;
	case pet_expr_binary:
		fprintf(stderr, "%s\n", op_str[expr->op]);
		expr_dump(expr->args[pet_bin_lhs], indent + 2);
		expr_dump(expr->args[pet_bin_rhs], indent + 2);
		break;
	case pet_expr_ternary:
		fprintf(stderr, "?:\n");
		expr_dump(expr->args[pet_ter_cond], indent + 2);
		expr_dump(expr->args[pet_ter_true], indent + 2);
		expr_dump(expr->args[pet_ter_false], indent + 2);
		break;
	case pet_expr_call:
		fprintf(stderr, "%s/%d\n", expr->name, expr->n_arg);
		for (i = 0; i < expr->n_arg; ++i)
			expr_dump(expr->args[i], indent + 2);
		break;
	}
}

void pet_expr_dump(struct pet_expr *expr)
{
	expr_dump(expr, 0);
}

/* Does "expr" represent an access to an unnamed space, i.e.,
 * does it represent an affine expression?
 */
int pet_expr_is_affine(struct pet_expr *expr)
{
	int has_id;

	if (!expr)
		return -1;
	if (expr->type != pet_expr_access)
		return 0;

	has_id = isl_map_has_tuple_id(expr->acc.access, isl_dim_out);
	if (has_id < 0)
		return -1;

	return !has_id;
}

/* Return 1 if the two pet_exprs are equivalent.
 */
int pet_expr_is_equal(struct pet_expr *expr1, struct pet_expr *expr2)
{
	int i;

	if (!expr1 || !expr2)
		return 0;

	if (expr1->type != expr2->type)
		return 0;
	if (expr1->n_arg != expr2->n_arg)
		return 0;
	for (i = 0; i < expr1->n_arg; ++i)
		if (!pet_expr_is_equal(expr1->args[i], expr2->args[i]))
			return 0;
	switch (expr1->type) {
	case pet_expr_double:
		if (expr1->d != expr2->d)
			return 0;
		break;
	case pet_expr_access:
		if (expr1->acc.read != expr2->acc.read)
			return 0;
		if (expr1->acc.write != expr2->acc.write)
			return 0;
		if (!expr1->acc.access || !expr2->acc.access)
			return 0;
		if (!isl_map_is_equal(expr1->acc.access, expr2->acc.access))
			return 0;
		break;
	case pet_expr_unary:
	case pet_expr_binary:
	case pet_expr_ternary:
		if (expr1->op != expr2->op)
			return 0;
		break;
	case pet_expr_call:
		if (strcmp(expr1->name, expr2->name))
			return 0;
		break;
	}

	return 1;
}

/* Add extra conditions on the parameters to all access relations in "expr".
 */
struct pet_expr *pet_expr_restrict(struct pet_expr *expr,
	__isl_take isl_set *cond)
{
	int i;

	if (!expr)
		goto error;

	for (i = 0; i < expr->n_arg; ++i) {
		expr->args[i] = pet_expr_restrict(expr->args[i],
							isl_set_copy(cond));
		if (!expr->args[i])
			goto error;
	}

	if (expr->type == pet_expr_access) {
		expr->acc.access = isl_map_intersect_params(expr->acc.access,
							    isl_set_copy(cond));
		if (!expr->acc.access)
			goto error;
	}

	isl_set_free(cond);
	return expr;
error:
	isl_set_free(cond);
	return pet_expr_free(expr);
}

/* Modify all access relations in "expr" by calling "fn" on them.
 */
struct pet_expr *pet_expr_foreach_access(struct pet_expr *expr,
	__isl_give isl_map *(*fn)(__isl_take isl_map *access, void *user),
	void *user)
{
	int i;

	if (!expr)
		return NULL;

	for (i = 0; i < expr->n_arg; ++i) {
		expr->args[i] = pet_expr_foreach_access(expr->args[i], fn, user);
		if (!expr->args[i])
			return pet_expr_free(expr);
	}

	if (expr->type == pet_expr_access) {
		expr->acc.access = fn(expr->acc.access, user);
		if (!expr->acc.access)
			return pet_expr_free(expr);
	}

	return expr;
}

/* Modify all expressions of type pet_expr_access in "expr"
 * by calling "fn" on them.
 */
struct pet_expr *pet_expr_foreach_access_expr(struct pet_expr *expr,
	struct pet_expr *(*fn)(struct pet_expr *expr, void *user),
	void *user)
{
	int i;

	if (!expr)
		return NULL;

	for (i = 0; i < expr->n_arg; ++i) {
		expr->args[i] = pet_expr_foreach_access_expr(expr->args[i],
								fn, user);
		if (!expr->args[i])
			return pet_expr_free(expr);
	}

	if (expr->type == pet_expr_access)
		expr = fn(expr, user);

	return expr;
}

/* Modify the given access relation based on the given iteration space
 * transformation.
 * If the access has any arguments then the domain of the access relation
 * is a wrapped mapping from the iteration space to the space of
 * argument values.  We only need to change the domain of this wrapped
 * mapping, so we extend the input transformation with an identity mapping
 * on the space of argument values.
 */
static __isl_give isl_map *update_domain(__isl_take isl_map *access,
	void *user)
{
	isl_map *update = user;
	isl_space *dim;

	update = isl_map_copy(update);

	dim = isl_map_get_space(access);
	dim = isl_space_domain(dim);
	if (!isl_space_is_wrapping(dim))
		isl_space_free(dim);
	else {
		isl_map *id;
		dim = isl_space_unwrap(dim);
		dim = isl_space_range(dim);
		dim = isl_space_map_from_set(dim);
		id = isl_map_identity(dim);
		update = isl_map_product(update, id);
	}

	return isl_map_apply_domain(access, update);
}

/* Modify all access relations in "expr" based on the given iteration space
 * transformation.
 */
static struct pet_expr *expr_update_domain(struct pet_expr *expr,
	__isl_take isl_map *update)
{
	expr = pet_expr_foreach_access(expr, &update_domain, update);
	isl_map_free(update);
	return expr;
}

/* Construct a pet_stmt with given line number and statement
 * number from a pet_expr.
 * The initial iteration domain is the zero-dimensional universe.
 * The name of the domain is given by "label" if it is non-NULL.
 * Otherwise, the name is constructed as S_<id>.
 * The domains of all access relations are modified to refer
 * to the statement iteration domain.
 */
struct pet_stmt *pet_stmt_from_pet_expr(isl_ctx *ctx, int line,
	__isl_take isl_id *label, int id, struct pet_expr *expr)
{
	struct pet_stmt *stmt;
	isl_space *dim;
	isl_set *dom;
	isl_map *sched;
	isl_map *add_name;
	char name[50];

	if (!expr)
		goto error;

	stmt = isl_calloc_type(ctx, struct pet_stmt);
	if (!stmt)
		goto error;

	dim = isl_space_set_alloc(ctx, 0, 0);
	if (label)
		dim = isl_space_set_tuple_id(dim, isl_dim_set, label);
	else {
		snprintf(name, sizeof(name), "S_%d", id);
		dim = isl_space_set_tuple_name(dim, isl_dim_set, name);
	}
	dom = isl_set_universe(isl_space_copy(dim));
	sched = isl_map_from_domain(isl_set_copy(dom));

	dim = isl_space_from_range(dim);
	add_name = isl_map_universe(dim);
	expr = expr_update_domain(expr, add_name);

	stmt->line = line;
	stmt->domain = dom;
	stmt->schedule = sched;
	stmt->body = expr;

	if (!stmt->domain || !stmt->schedule || !stmt->body)
		return pet_stmt_free(stmt);

	return stmt;
error:
	isl_id_free(label);
	return pet_expr_free(expr);
}

void *pet_stmt_free(struct pet_stmt *stmt)
{
	int i;

	if (!stmt)
		return NULL;

	isl_set_free(stmt->domain);
	isl_map_free(stmt->schedule);
	pet_expr_free(stmt->body);

	for (i = 0; i < stmt->n_arg; ++i)
		pet_expr_free(stmt->args[i]);
	free(stmt->args);

	free(stmt);
	return NULL;
}

static void stmt_dump(struct pet_stmt *stmt, int indent)
{
	int i;

	if (!stmt)
		return;

	fprintf(stderr, "%*s%d\n", indent, "", stmt->line);
	fprintf(stderr, "%*s", indent, "");
	isl_set_dump(stmt->domain);
	fprintf(stderr, "%*s", indent, "");
	isl_map_dump(stmt->schedule);
	expr_dump(stmt->body, indent);
	for (i = 0; i < stmt->n_arg; ++i)
		expr_dump(stmt->args[i], indent + 2);
}

void pet_stmt_dump(struct pet_stmt *stmt)
{
	stmt_dump(stmt, 0);
}

void *pet_array_free(struct pet_array *array)
{
	if (!array)
		return NULL;

	isl_set_free(array->context);
	isl_set_free(array->extent);
	isl_set_free(array->value_bounds);
	free(array->element_type);

	free(array);
	return NULL;
}

void pet_array_dump(struct pet_array *array)
{
	if (!array)
		return;

	isl_set_dump(array->context);
	isl_set_dump(array->extent);
	isl_set_dump(array->value_bounds);
	fprintf(stderr, "%s %s\n", array->element_type,
		array->live_out ? "live-out" : "");
}

/* Alloc a pet_scop structure, with extra room for information that
 * is only used during parsing.
 */
struct pet_scop *pet_scop_alloc(isl_ctx *ctx)
{
	return &isl_calloc_type(ctx, struct pet_scop_ext)->scop;
}

/* Construct a pet_scop with room for n statements.
 */
static struct pet_scop *scop_alloc(isl_ctx *ctx, int n)
{
	isl_space *space;
	struct pet_scop *scop;

	scop = pet_scop_alloc(ctx);
	if (!scop)
		return NULL;

	space = isl_space_params_alloc(ctx, 0);
	scop->context = isl_set_universe(isl_space_copy(space));
	scop->context_value = isl_set_universe(space);
	scop->stmts = isl_calloc_array(ctx, struct pet_stmt *, n);
	if (!scop->context || !scop->stmts)
		return pet_scop_free(scop);

	scop->n_stmt = n;

	return scop;
}

struct pet_scop *pet_scop_empty(isl_ctx *ctx)
{
	return scop_alloc(ctx, 0);
}

/* Update "context" with respect to the valid parameter values for "access".
 */
static __isl_give isl_set *access_extract_context(__isl_keep isl_map *access,
	__isl_take isl_set *context)
{
	context = isl_set_intersect(context,
					isl_map_params(isl_map_copy(access)));
	return context;
}

/* Update "context" with respect to the valid parameter values for "expr".
 *
 * If "expr" represents a ternary operator, then a parameter value
 * needs to be valid for the condition and for at least one of the
 * remaining two arguments.
 * If the condition is an affine expression, then we can be a bit more specific.
 * The parameter then has to be valid for the second argument for
 * non-zero accesses and valid for the third argument for zero accesses.
 */
static __isl_give isl_set *expr_extract_context(struct pet_expr *expr,
	__isl_take isl_set *context)
{
	int i;

	if (expr->type == pet_expr_ternary) {
		int is_aff;
		isl_set *context1, *context2;

		is_aff = pet_expr_is_affine(expr->args[0]);
		if (is_aff < 0)
			goto error;

		context = expr_extract_context(expr->args[0], context);
		context1 = expr_extract_context(expr->args[1],
						isl_set_copy(context));
		context2 = expr_extract_context(expr->args[2], context);

		if (is_aff) {
			isl_map *access;
			isl_set *zero_set;

			access = isl_map_copy(expr->args[0]->acc.access);
			access = isl_map_fix_si(access, isl_dim_out, 0, 0);
			zero_set = isl_map_params(access);
			context1 = isl_set_subtract(context1,
						    isl_set_copy(zero_set));
			context2 = isl_set_intersect(context2, zero_set);
		}

		context = isl_set_union(context1, context2);
		context = isl_set_coalesce(context);

		return context;
	}

	for (i = 0; i < expr->n_arg; ++i)
		context = expr_extract_context(expr->args[i], context);

	if (expr->type == pet_expr_access)
		context = access_extract_context(expr->acc.access, context);

	return context;
error:
	isl_set_free(context);
	return NULL;
}

/* Update "context" with respect to the valid parameter values for "stmt".
 */
static __isl_give isl_set *stmt_extract_context(struct pet_stmt *stmt,
	__isl_take isl_set *context)
{
	int i;

	for (i = 0; i < stmt->n_arg; ++i)
		context = expr_extract_context(stmt->args[i], context);

	context = expr_extract_context(stmt->body, context);

	return context;
}

/* Construct a pet_scop that contains the given pet_stmt.
 */
struct pet_scop *pet_scop_from_pet_stmt(isl_ctx *ctx, struct pet_stmt *stmt)
{
	struct pet_scop *scop;

	if (!stmt)
		return NULL;

	scop = scop_alloc(ctx, 1);

	scop->context = stmt_extract_context(stmt, scop->context);
	if (!scop->context)
		goto error;

	scop->stmts[0] = stmt;

	return scop;
error:
	pet_stmt_free(stmt);
	pet_scop_free(scop);
	return NULL;
}

/* Does "set" represent an element of an unnamed space, i.e.,
 * does it represent an affine expression?
 */
static int set_is_affine(__isl_keep isl_set *set)
{
	int has_id;

	has_id = isl_set_has_tuple_id(set);
	if (has_id < 0)
		return -1;

	return !has_id;
}

/* Combine ext1->skip[type] and ext2->skip[type] into ext->skip[type].
 * ext may be equal to either ext1 or ext2.
 *
 * The two skips that need to be combined are assumed to be affine expressions.
 *
 * We need to skip in ext if we need to skip in either ext1 or ext2.
 * We don't need to skip in ext if we don't need to skip in both ext1 and ext2.
 */
static struct pet_scop_ext *combine_skips(struct pet_scop_ext *ext,
	struct pet_scop_ext *ext1, struct pet_scop_ext *ext2,
	enum pet_skip type)
{
	isl_set *set, *skip1, *skip2;

	if (!ext)
		return NULL;
	if (!ext1->skip[type] && !ext2->skip[type])
		return ext;
	if (!ext1->skip[type]) {
		if (ext == ext2)
			return ext;
		ext->skip[type] = ext2->skip[type];
		ext2->skip[type] = NULL;
		return ext;
	}
	if (!ext2->skip[type]) {
		if (ext == ext1)
			return ext;
		ext->skip[type] = ext1->skip[type];
		ext1->skip[type] = NULL;
		return ext;
	}

	if (!set_is_affine(ext1->skip[type]) ||
	    !set_is_affine(ext2->skip[type]))
		isl_die(isl_set_get_ctx(ext1->skip[type]), isl_error_internal,
			"can only combine affine skips",
			return pet_scop_free(&ext->scop));

	skip1 = isl_set_copy(ext1->skip[type]);
	skip2 = isl_set_copy(ext2->skip[type]);
	set = isl_set_intersect(
			isl_set_fix_si(isl_set_copy(skip1), isl_dim_set, 0, 0),
			isl_set_fix_si(isl_set_copy(skip2), isl_dim_set, 0, 0));
	set = isl_set_union(set, isl_set_fix_si(skip1, isl_dim_set, 0, 1));
	set = isl_set_union(set, isl_set_fix_si(skip2, isl_dim_set, 0, 1));
	set = isl_set_coalesce(set);
	isl_set_free(ext1->skip[type]);
	ext1->skip[type] = NULL;
	isl_set_free(ext2->skip[type]);
	ext2->skip[type] = NULL;
	ext->skip[type] = set;
	if (!ext->skip[type])
		return pet_scop_free(&ext->scop);

	return ext;
}

/* Combine scop1->skip[type] and scop2->skip[type] into scop->skip[type],
 * where type takes on the values pet_skip_now and pet_skip_later.
 * scop may be equal to either scop1 or scop2.
 */
static struct pet_scop *scop_combine_skips(struct pet_scop *scop,
	struct pet_scop *scop1, struct pet_scop *scop2)
{
	struct pet_scop_ext *ext = (struct pet_scop_ext *) scop;
	struct pet_scop_ext *ext1 = (struct pet_scop_ext *) scop1;
	struct pet_scop_ext *ext2 = (struct pet_scop_ext *) scop2;

	ext = combine_skips(ext, ext1, ext2, pet_skip_now);
	ext = combine_skips(ext, ext1, ext2, pet_skip_later);
	return &ext->scop;
}

/* Construct a pet_scop that contains the arrays, statements and
 * skip information in "scop1" and "scop2".
 */
static struct pet_scop *pet_scop_add(isl_ctx *ctx, struct pet_scop *scop1,
	struct pet_scop *scop2)
{
	int i;
	struct pet_scop *scop;

	if (!scop1 || !scop2)
		goto error;

	if (scop1->n_stmt == 0) {
		scop2 = scop_combine_skips(scop2, scop1, scop2);
		pet_scop_free(scop1);
		return scop2;
	}

	if (scop2->n_stmt == 0) {
		scop1 = scop_combine_skips(scop1, scop1, scop2);
		pet_scop_free(scop2);
		return scop1;
	}

	scop = scop_alloc(ctx, scop1->n_stmt + scop2->n_stmt);
	if (!scop)
		goto error;

	scop->arrays = isl_calloc_array(ctx, struct pet_array *,
					scop1->n_array + scop2->n_array);
	if (!scop->arrays)
		goto error;
	scop->n_array = scop1->n_array + scop2->n_array;

	for (i = 0; i < scop1->n_stmt; ++i) {
		scop->stmts[i] = scop1->stmts[i];
		scop1->stmts[i] = NULL;
	}

	for (i = 0; i < scop2->n_stmt; ++i) {
		scop->stmts[scop1->n_stmt + i] = scop2->stmts[i];
		scop2->stmts[i] = NULL;
	}

	for (i = 0; i < scop1->n_array; ++i) {
		scop->arrays[i] = scop1->arrays[i];
		scop1->arrays[i] = NULL;
	}

	for (i = 0; i < scop2->n_array; ++i) {
		scop->arrays[scop1->n_array + i] = scop2->arrays[i];
		scop2->arrays[i] = NULL;
	}

	scop = pet_scop_restrict_context(scop, isl_set_copy(scop1->context));
	scop = pet_scop_restrict_context(scop, isl_set_copy(scop2->context));
	scop = scop_combine_skips(scop, scop1, scop2);

	pet_scop_free(scop1);
	pet_scop_free(scop2);
	return scop;
error:
	pet_scop_free(scop1);
	pet_scop_free(scop2);
	return NULL;
}

/* Apply the skip condition "skip" to "scop".
 * That is, make sure "scop" is not executed when the condition holds.
 *
 * If "skip" is an affine expression, we add the conditions under
 * which the expression is zero to the iteration domains.
 * Otherwise, we add a filter on the variable attaining the value zero.
 */
static struct pet_scop *restrict_skip(struct pet_scop *scop,
	__isl_take isl_set *skip)
{
	isl_map *skip_map;
	int is_aff;

	if (!scop || !skip)
		goto error;

	is_aff = set_is_affine(skip);
	if (is_aff < 0)
		goto error;

	if (!is_aff)
		return pet_scop_filter(scop, isl_map_from_range(skip), 0);

	skip = isl_set_fix_si(skip, isl_dim_set, 0, 0);
	scop = pet_scop_restrict(scop, isl_set_params(skip));

	return scop;
error:
	isl_set_free(skip);
	return pet_scop_free(scop);
}

/* Construct a pet_scop that contains the arrays, statements and
 * skip information in "scop1" and "scop2", where the two scops
 * are executed "in sequence".  That is, breaks and continues
 * in scop1 have an effect on scop2.
 */
struct pet_scop *pet_scop_add_seq(isl_ctx *ctx, struct pet_scop *scop1,
	struct pet_scop *scop2)
{
	if (scop1 && pet_scop_has_skip(scop1, pet_skip_now))
		scop2 = restrict_skip(scop2,
					pet_scop_get_skip(scop1, pet_skip_now));
	return pet_scop_add(ctx, scop1, scop2);
}

/* Construct a pet_scop that contains the arrays, statements and
 * skip information in "scop1" and "scop2", where the two scops
 * are executed "in parallel".  That is, any break or continue
 * in scop1 has no effect on scop2.
 */
struct pet_scop *pet_scop_add_par(isl_ctx *ctx, struct pet_scop *scop1,
	struct pet_scop *scop2)
{
	return pet_scop_add(ctx, scop1, scop2);
}

void *pet_scop_free(struct pet_scop *scop)
{
	int i;
	struct pet_scop_ext *ext = (struct pet_scop_ext *) scop;

	if (!scop)
		return NULL;
	isl_set_free(scop->context);
	isl_set_free(scop->context_value);
	if (scop->arrays)
		for (i = 0; i < scop->n_array; ++i)
			pet_array_free(scop->arrays[i]);
	free(scop->arrays);
	if (scop->stmts)
		for (i = 0; i < scop->n_stmt; ++i)
			pet_stmt_free(scop->stmts[i]);
	free(scop->stmts);
	isl_set_free(ext->skip[pet_skip_now]);
	isl_set_free(ext->skip[pet_skip_later]);
	free(scop);
	return NULL;
}

void pet_scop_dump(struct pet_scop *scop)
{
	int i;
	struct pet_scop_ext *ext = (struct pet_scop_ext *) scop;

	if (!scop)
		return;
	
	isl_set_dump(scop->context);
	isl_set_dump(scop->context_value);
	for (i = 0; i < scop->n_array; ++i)
		pet_array_dump(scop->arrays[i]);
	for (i = 0; i < scop->n_stmt; ++i)
		pet_stmt_dump(scop->stmts[i]);

	if (ext->skip[0]) {
		fprintf(stderr, "skip\n");
		isl_set_dump(ext->skip[0]);
		isl_set_dump(ext->skip[1]);
	}
}

/* Return 1 if the two pet_arrays are equivalent.
 *
 * We don't compare element_size as this may be target dependent.
 */
int pet_array_is_equal(struct pet_array *array1, struct pet_array *array2)
{
	if (!array1 || !array2)
		return 0;

	if (!isl_set_is_equal(array1->context, array2->context))
		return 0;
	if (!isl_set_is_equal(array1->extent, array2->extent))
		return 0;
	if (!!array1->value_bounds != !!array2->value_bounds)
		return 0;
	if (array1->value_bounds &&
	    !isl_set_is_equal(array1->value_bounds, array2->value_bounds))
		return 0;
	if (strcmp(array1->element_type, array2->element_type))
		return 0;
	if (array1->live_out != array2->live_out)
		return 0;
	if (array1->uniquely_defined != array2->uniquely_defined)
		return 0;

	return 1;
}

/* Return 1 if the two pet_stmts are equivalent.
 */
int pet_stmt_is_equal(struct pet_stmt *stmt1, struct pet_stmt *stmt2)
{
	int i;

	if (!stmt1 || !stmt2)
		return 0;
	
	if (stmt1->line != stmt2->line)
		return 0;
	if (!isl_set_is_equal(stmt1->domain, stmt2->domain))
		return 0;
	if (!isl_map_is_equal(stmt1->schedule, stmt2->schedule))
		return 0;
	if (!pet_expr_is_equal(stmt1->body, stmt2->body))
		return 0;
	if (stmt1->n_arg != stmt2->n_arg)
		return 0;
	for (i = 0; i < stmt1->n_arg; ++i) {
		if (!pet_expr_is_equal(stmt1->args[i], stmt2->args[i]))
			return 0;
	}

	return 1;
}

/* Return 1 if the two pet_scops are equivalent.
 */
int pet_scop_is_equal(struct pet_scop *scop1, struct pet_scop *scop2)
{
	int i;

	if (!scop1 || !scop2)
		return 0;

	if (!isl_set_is_equal(scop1->context, scop2->context))
		return 0;
	if (!isl_set_is_equal(scop1->context_value, scop2->context_value))
		return 0;

	if (scop1->n_array != scop2->n_array)
		return 0;
	for (i = 0; i < scop1->n_array; ++i)
		if (!pet_array_is_equal(scop1->arrays[i], scop2->arrays[i]))
			return 0;

	if (scop1->n_stmt != scop2->n_stmt)
		return 0;
	for (i = 0; i < scop1->n_stmt; ++i)
		if (!pet_stmt_is_equal(scop1->stmts[i], scop2->stmts[i]))
			return 0;

	return 1;
}

/* Prefix the schedule of "stmt" with an extra dimension with constant
 * value "pos".
 */
struct pet_stmt *pet_stmt_prefix(struct pet_stmt *stmt, int pos)
{
	if (!stmt)
		return NULL;

	stmt->schedule = isl_map_insert_dims(stmt->schedule, isl_dim_out, 0, 1);
	stmt->schedule = isl_map_fix_si(stmt->schedule, isl_dim_out, 0, pos);
	if (!stmt->schedule)
		return pet_stmt_free(stmt);

	return stmt;
}

/* Prefix the schedules of all statements in "scop" with an extra
 * dimension with constant value "pos".
 */
struct pet_scop *pet_scop_prefix(struct pet_scop *scop, int pos)
{
	int i;

	if (!scop)
		return NULL;

	for (i = 0; i < scop->n_stmt; ++i) {
		scop->stmts[i] = pet_stmt_prefix(scop->stmts[i], pos);
		if (!scop->stmts[i])
			return pet_scop_free(scop);
	}

	return scop;
}

/* Given a set with a parameter at "param_pos" that refers to the
 * iterator, "move" the iterator to the first set dimension.
 * That is, essentially equate the parameter to the first set dimension
 * and then project it out.
 *
 * The first set dimension may however refer to a virtual iterator,
 * while the parameter refers to the "real" iterator.
 * We therefore need to take into account the mapping "iv_map", which
 * maps the virtual iterator to the real iterator.
 * In particular, we equate the set dimension to the input of the map
 * and the parameter to the output of the map and then project out
 * everything we don't need anymore.
 */
static __isl_give isl_set *internalize_iv(__isl_take isl_set *set,
	int param_pos, __isl_take isl_map *iv_map)
{
	isl_map *map;
	map = isl_map_from_domain(set);
	map = isl_map_add_dims(map, isl_dim_out, 1);
	map = isl_map_equate(map, isl_dim_in, 0, isl_dim_out, 0);
	iv_map = isl_map_align_params(iv_map, isl_map_get_space(map));
	map = isl_map_apply_range(map, iv_map);
	map = isl_map_equate(map, isl_dim_param, param_pos, isl_dim_out, 0);
	map = isl_map_project_out(map, isl_dim_param, param_pos, 1);
	return isl_map_domain(map);
}

/* Data used in embed_access.
 * extend adds an iterator to the iteration domain
 * iv_map maps the virtual iterator to the real iterator
 * var_id represents the induction variable of the corresponding loop
 */
struct pet_embed_access {
	isl_map *extend;
	isl_map *iv_map;
	isl_id *var_id;
};

/* Embed the access relation in an extra outer loop.
 *
 * We first update the iteration domain to insert the extra dimension.
 *
 * If the access refers to the induction variable, then it is
 * turned into an access to the set of integers with index (and value)
 * equal to the induction variable.
 *
 * If the induction variable appears in the constraints (as a parameter),
 * then the parameter is equated to the newly introduced iteration
 * domain dimension and subsequently projected out.
 *
 * Similarly, if the accessed array is a virtual array (with user
 * pointer equal to NULL), as created by create_test_access,
 * then it is extended along with the domain of the access.
 */
static __isl_give isl_map *embed_access(__isl_take isl_map *access,
	void *user)
{
	struct pet_embed_access *data = user;
	isl_id *array_id = NULL;
	int pos;

	access = update_domain(access, data->extend);

	if (isl_map_has_tuple_id(access, isl_dim_out))
		array_id = isl_map_get_tuple_id(access, isl_dim_out);
	if (array_id == data->var_id ||
	    (array_id && !isl_id_get_user(array_id))) {
		access = isl_map_insert_dims(access, isl_dim_out, 0, 1);
		access = isl_map_equate(access,
					isl_dim_in, 0, isl_dim_out, 0);
		if (array_id == data->var_id)
			access = isl_map_apply_range(access,
						isl_map_copy(data->iv_map));
		else
			access = isl_map_set_tuple_id(access, isl_dim_out,
							isl_id_copy(array_id));
	}
	isl_id_free(array_id);

	pos = isl_map_find_dim_by_id(access, isl_dim_param, data->var_id);
	if (pos >= 0) {
		isl_set *set = isl_map_wrap(access);
		set = internalize_iv(set, pos, isl_map_copy(data->iv_map));
		access = isl_set_unwrap(set);
	}
	access = isl_map_set_dim_id(access, isl_dim_in, 0,
					isl_id_copy(data->var_id));

	return access;
}

/* Embed all access relations in "expr" in an extra loop.
 * "extend" inserts an outer loop iterator in the iteration domains.
 * "iv_map" maps the virtual iterator to the real iterator
 * "var_id" represents the induction variable.
 */
static struct pet_expr *expr_embed(struct pet_expr *expr,
	__isl_take isl_map *extend, __isl_take isl_map *iv_map,
	__isl_keep isl_id *var_id)
{
	struct pet_embed_access data =
		{ .extend = extend, .iv_map = iv_map, .var_id = var_id };

	expr = pet_expr_foreach_access(expr, &embed_access, &data);
	isl_map_free(iv_map);
	isl_map_free(extend);
	return expr;
}

/* Embed the given pet_stmt in an extra outer loop with iteration domain
 * "dom" and schedule "sched".  "var_id" represents the induction variable
 * of the loop.  "iv_map" maps a possibly virtual iterator to the real iterator.
 * That is, it maps the iterator used in "dom" and the domain of "sched"
 * to the iterator that some of the parameters in "stmt" may refer to.
 *
 * The iteration domain and schedule of the statement are updated
 * according to the iteration domain and schedule of the new loop.
 * If stmt->domain is a wrapped map, then the iteration domain
 * is the domain of this map, so we need to be careful to adjust
 * this domain.
 *
 * If the induction variable appears in the constraints (as a parameter)
 * of the current iteration domain or the schedule of the statement,
 * then the parameter is equated to the newly introduced iteration
 * domain dimension and subsequently projected out.
 *
 * Finally, all access relations are updated based on the extra loop.
 */
static struct pet_stmt *pet_stmt_embed(struct pet_stmt *stmt,
	__isl_take isl_set *dom, __isl_take isl_map *sched,
	__isl_take isl_map *iv_map, __isl_take isl_id *var_id)
{
	int i;
	int pos;
	isl_id *stmt_id;
	isl_space *dim;
	isl_map *extend;

	if (!stmt)
		goto error;

	if (isl_set_is_wrapping(stmt->domain)) {
		isl_map *map;
		isl_map *ext;
		isl_space *ran_dim;

		map = isl_set_unwrap(stmt->domain);
		stmt_id = isl_map_get_tuple_id(map, isl_dim_in);
		ran_dim = isl_space_range(isl_map_get_space(map));
		ext = isl_map_from_domain_and_range(isl_set_copy(dom),
						    isl_set_universe(ran_dim));
		map = isl_map_flat_domain_product(ext, map);
		map = isl_map_set_tuple_id(map, isl_dim_in,
							isl_id_copy(stmt_id));
		dim = isl_space_domain(isl_map_get_space(map));
		stmt->domain = isl_map_wrap(map);
	} else {
		stmt_id = isl_set_get_tuple_id(stmt->domain);
		stmt->domain = isl_set_flat_product(isl_set_copy(dom),
						    stmt->domain);
		stmt->domain = isl_set_set_tuple_id(stmt->domain,
							isl_id_copy(stmt_id));
		dim = isl_set_get_space(stmt->domain);
	}

	pos = isl_set_find_dim_by_id(stmt->domain, isl_dim_param, var_id);
	if (pos >= 0)
		stmt->domain = internalize_iv(stmt->domain, pos,
						isl_map_copy(iv_map));

	stmt->schedule = isl_map_flat_product(sched, stmt->schedule);
	stmt->schedule = isl_map_set_tuple_id(stmt->schedule,
						isl_dim_in, stmt_id);

	pos = isl_map_find_dim_by_id(stmt->schedule, isl_dim_param, var_id);
	if (pos >= 0) {
		isl_set *set = isl_map_wrap(stmt->schedule);
		set = internalize_iv(set, pos, isl_map_copy(iv_map));
		stmt->schedule = isl_set_unwrap(set);
	}

	dim = isl_space_map_from_set(dim);
	extend = isl_map_identity(dim);
	extend = isl_map_remove_dims(extend, isl_dim_in, 0, 1);
	extend = isl_map_set_tuple_id(extend, isl_dim_in,
				    isl_map_get_tuple_id(extend, isl_dim_out));
	for (i = 0; i < stmt->n_arg; ++i)
		stmt->args[i] = expr_embed(stmt->args[i], isl_map_copy(extend),
					    isl_map_copy(iv_map), var_id);
	stmt->body = expr_embed(stmt->body, extend, iv_map, var_id);

	isl_set_free(dom);
	isl_id_free(var_id);

	for (i = 0; i < stmt->n_arg; ++i)
		if (!stmt->args[i])
			return pet_stmt_free(stmt);
	if (!stmt->domain || !stmt->schedule || !stmt->body)
		return pet_stmt_free(stmt);
	return stmt;
error:
	isl_set_free(dom);
	isl_map_free(sched);
	isl_map_free(iv_map);
	isl_id_free(var_id);
	return NULL;
}

/* Embed the given pet_array in an extra outer loop with iteration domain
 * "dom".
 * This embedding only has an effect on virtual arrays (those with
 * user pointer equal to NULL), which need to be extended along with
 * the iteration domain.
 */
static struct pet_array *pet_array_embed(struct pet_array *array,
	__isl_take isl_set *dom)
{
	isl_id *array_id = NULL;

	if (!array)
		goto error;

	if (isl_set_has_tuple_id(array->extent))
		array_id = isl_set_get_tuple_id(array->extent);

	if (array_id && !isl_id_get_user(array_id)) {
		array->extent = isl_set_flat_product(dom, array->extent);
		array->extent = isl_set_set_tuple_id(array->extent, array_id);
	} else {
		isl_set_free(dom);
		isl_id_free(array_id);
	}

	return array;
error:
	isl_set_free(dom);
	return NULL;
}

/* Project out all unnamed parameters from "set" and return the result.
 */
static __isl_give isl_set *set_project_out_unnamed_params(
	__isl_take isl_set *set)
{
	int i, n;

	n = isl_set_dim(set, isl_dim_param);
	for (i = n - 1; i >= 0; --i) {
		if (isl_set_has_dim_name(set, isl_dim_param, i))
			continue;
		set = isl_set_project_out(set, isl_dim_param, i, 1);
	}

	return set;
}

/* Update the context with respect to an embedding into a loop
 * with iteration domain "dom" and induction variable "id".
 * "iv_map" maps a possibly virtual iterator (used in "dom")
 * to the real iterator (parameter "id").
 *
 * If the current context is independent of "id", we don't need
 * to do anything.
 * Otherwise, a parameter value is invalid for the embedding if
 * any of the corresponding iterator values is invalid.
 * That is, a parameter value is valid only if all the corresponding
 * iterator values are valid.
 * We therefore compute the set of parameters
 *
 *	forall i in dom : valid (i)
 *
 * or
 *
 *	not exists i in dom : not valid(i)
 *
 * i.e.,
 *
 *	not exists i in dom \ valid(i)
 *
 * Before we subtract valid(i) from dom, we first need to map
 * the real iterator to the virtual iterator.
 *
 * If there are any unnamed parameters in "dom", then we consider
 * a parameter value to be valid if it is valid for any value of those
 * unnamed parameters.  They are therefore projected out at the end.
 */
static __isl_give isl_set *context_embed(__isl_take isl_set *context,
	__isl_keep isl_set *dom, __isl_keep isl_map *iv_map,
	__isl_keep isl_id *id)
{
	int pos;

	pos = isl_set_find_dim_by_id(context, isl_dim_param, id);
	if (pos < 0)
		return context;

	context = isl_set_from_params(context);
	context = isl_set_add_dims(context, isl_dim_set, 1);
	context = isl_set_equate(context, isl_dim_param, pos, isl_dim_set, 0);
	context = isl_set_project_out(context, isl_dim_param, pos, 1);
	context = isl_set_apply(context, isl_map_reverse(isl_map_copy(iv_map)));
	context = isl_set_subtract(isl_set_copy(dom), context);
	context = isl_set_params(context);
	context = isl_set_complement(context);
	context = set_project_out_unnamed_params(context);
	return context;
}

/* Embed all statements and arrays in "scop" in an extra outer loop
 * with iteration domain "dom" and schedule "sched".
 * "id" represents the induction variable of the loop.
 * "iv_map" maps a possibly virtual iterator to the real iterator.
 * That is, it maps the iterator used in "dom" and the domain of "sched"
 * to the iterator that some of the parameters in "scop" may refer to.
 *
 * Any skip conditions within the loop have no effect outside of the loop.
 * The caller is responsible for making sure skip[pet_skip_later] has been
 * taken into account.
 */
struct pet_scop *pet_scop_embed(struct pet_scop *scop, __isl_take isl_set *dom,
	__isl_take isl_map *sched, __isl_take isl_map *iv_map,
	__isl_take isl_id *id)
{
	int i;

	if (!scop)
		goto error;

	pet_scop_reset_skip(scop, pet_skip_now);
	pet_scop_reset_skip(scop, pet_skip_later);

	scop->context = context_embed(scop->context, dom, iv_map, id);
	if (!scop->context)
		goto error;

	for (i = 0; i < scop->n_stmt; ++i) {
		scop->stmts[i] = pet_stmt_embed(scop->stmts[i],
					isl_set_copy(dom), isl_map_copy(sched),
					isl_map_copy(iv_map), isl_id_copy(id));
		if (!scop->stmts[i])
			goto error;
	}

	for (i = 0; i < scop->n_array; ++i) {
		scop->arrays[i] = pet_array_embed(scop->arrays[i],
					isl_set_copy(dom));
		if (!scop->arrays[i])
			goto error;
	}

	isl_set_free(dom);
	isl_map_free(sched);
	isl_map_free(iv_map);
	isl_id_free(id);
	return scop;
error:
	isl_set_free(dom);
	isl_map_free(sched);
	isl_map_free(iv_map);
	isl_id_free(id);
	return pet_scop_free(scop);
}

/* Add extra conditions on the parameters to iteration domain of "stmt".
 */
static struct pet_stmt *stmt_restrict(struct pet_stmt *stmt,
	__isl_take isl_set *cond)
{
	if (!stmt)
		goto error;

	stmt->domain = isl_set_intersect_params(stmt->domain, cond);

	return stmt;
error:
	isl_set_free(cond);
	return pet_stmt_free(stmt);
}

/* Add extra conditions to scop->skip[type].
 *
 * The new skip condition only holds if it held before
 * and the condition is true.  It does not hold if it did not hold
 * before or the condition is false.
 *
 * The skip condition is assumed to be an affine expression.
 */
static struct pet_scop *pet_scop_restrict_skip(struct pet_scop *scop,
	enum pet_skip type, __isl_keep isl_set *cond)
{
	struct pet_scop_ext *ext = (struct pet_scop_ext *) scop;
	isl_set *skip;
	isl_set *set;

	if (!scop)
		return NULL;
	if (!ext->skip[type])
		return scop;

	if (!set_is_affine(ext->skip[type]))
		isl_die(isl_set_get_ctx(ext->skip[type]), isl_error_internal,
			"can only resrict affine skips",
			return pet_scop_free(scop));

	skip = ext->skip[type];
	skip = isl_set_intersect_params(skip, isl_set_copy(cond));
	set = isl_set_from_params(isl_set_copy(cond));
	set = isl_set_complement(set);
	set = isl_set_add_dims(set, isl_dim_set, 1);
	set = isl_set_fix_si(set, isl_dim_set, 0, 0);
	skip = isl_set_union(skip, set);
	ext->skip[type] = skip;
	if (!ext->skip[type])
		return pet_scop_free(scop);

	return scop;
}

/* Add extra conditions on the parameters to all iteration domains
 * and skip conditions.
 *
 * A parameter value is valid for the result if it was valid
 * for the original scop and satisfies "cond" or if it does
 * not satisfy "cond" as in this case the scop is not executed
 * and the original constraints on the parameters are irrelevant.
 */
struct pet_scop *pet_scop_restrict(struct pet_scop *scop,
	__isl_take isl_set *cond)
{
	int i;

	scop = pet_scop_restrict_skip(scop, pet_skip_now, cond);
	scop = pet_scop_restrict_skip(scop, pet_skip_later, cond);

	if (!scop)
		goto error;

	scop->context = isl_set_intersect(scop->context, isl_set_copy(cond));
	scop->context = isl_set_union(scop->context,
				isl_set_complement(isl_set_copy(cond)));
	scop->context = isl_set_coalesce(scop->context);
	scop->context = set_project_out_unnamed_params(scop->context);
	if (!scop->context)
		goto error;

	for (i = 0; i < scop->n_stmt; ++i) {
		scop->stmts[i] = stmt_restrict(scop->stmts[i],
						    isl_set_copy(cond));
		if (!scop->stmts[i])
			goto error;
	}

	isl_set_free(cond);
	return scop;
error:
	isl_set_free(cond);
	return pet_scop_free(scop);
}

/* Construct a map that inserts a filter value with name "id" and value
 * "satisfied" in the list of filter values embedded in the set space "space".
 *
 * If "space" does not contain any filter values yet, we first create
 * a map that inserts 0 filter values, i.e.,
 *
 *	space -> [space -> []]
 *
 * We can now assume that space is of the form [dom -> [filters]]
 * We construct an identity mapping on dom and a mapping on filters
 * that inserts the new filter
 *
 *	dom -> dom
 *	[filters] -> [satisfied, filters]
 *
 * and then compute the cross product
 *
 *	[dom -> [filters]] -> [dom -> [satisfied, filters]]
 */
static __isl_give isl_map *insert_filter_map(__isl_take isl_space *space,
	__isl_take isl_id *id, int satisfied)
{
	isl_space *space2;
	isl_map *map, *map_dom, *map_ran;
	isl_set *dom;

	if (isl_space_is_wrapping(space)) {
		space2 = isl_space_map_from_set(isl_space_copy(space));
		map = isl_map_identity(space2);
		space = isl_space_unwrap(space);
	} else {
		space = isl_space_from_domain(space);
		map = isl_map_universe(isl_space_copy(space));
		map = isl_map_reverse(isl_map_domain_map(map));
	}

	space2 = isl_space_domain(isl_space_copy(space));
	map_dom = isl_map_identity(isl_space_map_from_set(space2));
	space = isl_space_range(space);
	map_ran = isl_map_identity(isl_space_map_from_set(space));
	map_ran = isl_map_insert_dims(map_ran, isl_dim_out, 0, 1);
	map_ran = isl_map_set_dim_id(map_ran, isl_dim_out, 0, id);
	map_ran = isl_map_fix_si(map_ran, isl_dim_out, 0, satisfied);

	map = isl_map_apply_range(map, isl_map_product(map_dom, map_ran));

	return map;
}

/* Insert an argument expression corresponding to "test" in front
 * of the list of arguments described by *n_arg and *args.
 */
static int args_insert_access(unsigned *n_arg, struct pet_expr ***args,
	__isl_keep isl_map *test)
{
	int i;
	isl_ctx *ctx = isl_map_get_ctx(test);

	if (!test)
		return -1;

	if (!*args) {
		*args = isl_calloc_array(ctx, struct pet_expr *, 1);
		if (!*args)
			return -1;
	} else {
		struct pet_expr **ext;
		ext = isl_calloc_array(ctx, struct pet_expr *, 1 + *n_arg);
		if (!ext)
			return -1;
		for (i = 0; i < *n_arg; ++i)
			ext[1 + i] = (*args)[i];
		free(*args);
		*args = ext;
	}
	(*n_arg)++;
	(*args)[0] = pet_expr_from_access(isl_map_copy(test));
	if (!(*args)[0])
		return -1;

	return 0;
}

/* Make the expression "expr" depend on the value of "test"
 * being equal to "satisfied".
 *
 * If "test" is an affine expression, we simply add the conditions
 * on the expression have the value "satisfied" to all access relations.
 *
 * Otherwise, we add a filter to "expr" (which is then assumed to be
 * an access expression) corresponding to "test" being equal to "satisfied".
 */
struct pet_expr *pet_expr_filter(struct pet_expr *expr,
	__isl_take isl_map *test, int satisfied)
{
	isl_id *id;
	isl_ctx *ctx;
	isl_space *space;
	isl_map *map;

	if (!expr || !test)
		goto error;

	if (!isl_map_has_tuple_id(test, isl_dim_out)) {
		test = isl_map_fix_si(test, isl_dim_out, 0, satisfied);
		return pet_expr_restrict(expr, isl_map_params(test));
	}

	ctx = isl_map_get_ctx(test);
	if (expr->type != pet_expr_access)
		isl_die(ctx, isl_error_invalid,
			"can only filter access expressions", goto error);

	space = isl_space_domain(isl_map_get_space(expr->acc.access));
	id = isl_map_get_tuple_id(test, isl_dim_out);
	map = insert_filter_map(space, id, satisfied);

	expr->acc.access = isl_map_apply_domain(expr->acc.access, map);
	if (!expr->acc.access)
		goto error;

	if (args_insert_access(&expr->n_arg, &expr->args, test) < 0)
		goto error;

	isl_map_free(test);
	return expr;
error:
	isl_map_free(test);
	return pet_expr_free(expr);
}

/* Make the statement "stmt" depend on the value of "test"
 * being equal to "satisfied" by adjusting stmt->domain.
 *
 * The domain of "test" corresponds to the (zero or more) outer dimensions
 * of the iteration domain.
 *
 * We insert an argument corresponding to a read to "test"
 * from the iteration domain of "stmt" in front of the list of arguments.
 * We also insert a corresponding output dimension in the wrapped
 * map contained in stmt->domain, with value set to "satisfied".
 */
static struct pet_stmt *stmt_filter(struct pet_stmt *stmt,
	__isl_take isl_map *test, int satisfied)
{
	int i;
	isl_id *id;
	isl_ctx *ctx;
	isl_map *map, *add_dom;
	isl_space *space;
	isl_set *dom;
	int n_test_dom;

	if (!stmt || !test)
		goto error;

	id = isl_map_get_tuple_id(test, isl_dim_out);
	map = insert_filter_map(isl_set_get_space(stmt->domain), id, satisfied);
	stmt->domain = isl_set_apply(stmt->domain, map);

	space = isl_space_unwrap(isl_set_get_space(stmt->domain));
	dom = isl_set_universe(isl_space_domain(space));
	n_test_dom = isl_map_dim(test, isl_dim_in);
	add_dom = isl_map_from_range(dom);
	add_dom = isl_map_add_dims(add_dom, isl_dim_in, n_test_dom);
	for (i = 0; i < n_test_dom; ++i)
		add_dom = isl_map_equate(add_dom, isl_dim_in, i,
						    isl_dim_out, i);
	test = isl_map_apply_domain(test, add_dom);

	if (args_insert_access(&stmt->n_arg, &stmt->args, test) < 0)
		goto error;

	isl_map_free(test);
	return stmt;
error:
	isl_map_free(test);
	return pet_stmt_free(stmt);
}

/* Does "scop" have a skip condition of the given "type"?
 */
int pet_scop_has_skip(struct pet_scop *scop, enum pet_skip type)
{
	struct pet_scop_ext *ext = (struct pet_scop_ext *) scop;

	if (!scop)
		return -1;
	return ext->skip[type] != NULL;
}

/* Does "scop" have a skip condition of the given "type" that
 * is an affine expression?
 */
int pet_scop_has_affine_skip(struct pet_scop *scop, enum pet_skip type)
{
	struct pet_scop_ext *ext = (struct pet_scop_ext *) scop;

	if (!scop)
		return -1;
	if (!ext->skip[type])
		return 0;
	return set_is_affine(ext->skip[type]);
}

/* Does "scop" have a skip condition of the given "type" that
 * is not an affine expression?
 */
int pet_scop_has_var_skip(struct pet_scop *scop, enum pet_skip type)
{
	struct pet_scop_ext *ext = (struct pet_scop_ext *) scop;
	int aff;

	if (!scop)
		return -1;
	if (!ext->skip[type])
		return 0;
	aff = set_is_affine(ext->skip[type]);
	if (aff < 0)
		return -1;
	return !aff;
}

/* Does "scop" have a skip condition of the given "type" that
 * is affine and holds on the entire domain?
 */
int pet_scop_has_universal_skip(struct pet_scop *scop, enum pet_skip type)
{
	struct pet_scop_ext *ext = (struct pet_scop_ext *) scop;
	isl_set *set;
	int is_aff;
	int is_univ;

	is_aff = pet_scop_has_affine_skip(scop, type);
	if (is_aff < 0 || !is_aff)
		return is_aff;

	set = isl_set_copy(ext->skip[type]);
	set = isl_set_fix_si(set, isl_dim_set, 0, 1);
	set = isl_set_params(set);
	is_univ = isl_set_plain_is_universe(set);
	isl_set_free(set);

	return is_univ;
}

/* Replace scop->skip[type] by "skip".
 */
struct pet_scop *pet_scop_set_skip(struct pet_scop *scop,
	enum pet_skip type, __isl_take isl_set *skip)
{
	struct pet_scop_ext *ext = (struct pet_scop_ext *) scop;

	if (!scop || !skip)
		goto error;

	isl_set_free(ext->skip[type]);
	ext->skip[type] = skip;

	return scop;
error:
	isl_set_free(skip);
	return pet_scop_free(scop);
}

/* Return a copy of scop->skip[type].
 */
__isl_give isl_set *pet_scop_get_skip(struct pet_scop *scop,
	enum pet_skip type)
{
	struct pet_scop_ext *ext = (struct pet_scop_ext *) scop;

	if (!scop)
		return NULL;

	return isl_set_copy(ext->skip[type]);
}

/* Return a map to the skip condition of the given type.
 */
__isl_give isl_map *pet_scop_get_skip_map(struct pet_scop *scop,
	enum pet_skip type)
{
	return isl_map_from_range(pet_scop_get_skip(scop, type));
}

/* Return an access pet_expr corresponding to the skip condition
 * of the given type.
 */
struct pet_expr *pet_scop_get_skip_expr(struct pet_scop *scop,
	enum pet_skip type)
{
	return pet_expr_from_access(pet_scop_get_skip_map(scop, type));
}

/* Drop the the skip condition scop->skip[type].
 */
void pet_scop_reset_skip(struct pet_scop *scop, enum pet_skip type)
{
	struct pet_scop_ext *ext = (struct pet_scop_ext *) scop;

	if (!scop)
		return;

	isl_set_free(ext->skip[type]);
	ext->skip[type] = NULL;
}

/* Make the skip condition (if any) depend on the value of "test" being
 * equal to "satisfied".
 *
 * We only support the case where the original skip condition is universal,
 * i.e., where skipping is unconditional, and where satisfied == 1.
 * In this case, the skip condition is changed to skip only when 
 * "test" is equal to one.
 */
static struct pet_scop *pet_scop_filter_skip(struct pet_scop *scop,
	enum pet_skip type, __isl_keep isl_map *test, int satisfied)
{
	int is_univ = 0;

	if (!scop)
		return NULL;
	if (!pet_scop_has_skip(scop, type))
		return scop;

	if (satisfied)
		is_univ = pet_scop_has_universal_skip(scop, type);
	if (is_univ < 0)
		return pet_scop_free(scop);
	if (satisfied && is_univ) {
		scop = pet_scop_set_skip(scop, type,
					 isl_map_range(isl_map_copy(test)));
		if (!scop)
			return NULL;
	} else {
		isl_die(isl_map_get_ctx(test), isl_error_internal,
			"skip expression cannot be filtered",
			return pet_scop_free(scop));
	}

	return scop;
}

/* Make all statements in "scop" depend on the value of "test"
 * being equal to "satisfied" by adjusting their domains.
 */
struct pet_scop *pet_scop_filter(struct pet_scop *scop,
	__isl_take isl_map *test, int satisfied)
{
	int i;

	scop = pet_scop_filter_skip(scop, pet_skip_now, test, satisfied);
	scop = pet_scop_filter_skip(scop, pet_skip_later, test, satisfied);

	if (!scop || !test)
		goto error;

	for (i = 0; i < scop->n_stmt; ++i) {
		scop->stmts[i] = stmt_filter(scop->stmts[i],
						isl_map_copy(test), satisfied);
		if (!scop->stmts[i])
			goto error;
	}

	isl_map_free(test);
	return scop;
error:
	isl_map_free(test);
	return pet_scop_free(scop);
}

/* Do the filters "i" and "j" always have the same value?
 */
static int equal_filter_values(__isl_keep isl_set *domain, int i, int j)
{
	isl_map *map, *test;
	int equal;

	map = isl_set_unwrap(isl_set_copy(domain));
	test = isl_map_universe(isl_map_get_space(map));
	test = isl_map_equate(test, isl_dim_out, i, isl_dim_out, j);
	equal = isl_map_is_subset(map, test);
	isl_map_free(map);
	isl_map_free(test);

	return equal;
}

/* Merge filters "i" and "j" into a single filter ("i") with as filter
 * access relation, the union of the two access relations.
 */
static struct pet_stmt *merge_filter_pair(struct pet_stmt *stmt, int i, int j)
{
	int k;
	isl_map *map;

	if (!stmt)
		return NULL;

	stmt->args[i]->acc.access = isl_map_union(stmt->args[i]->acc.access,
				    isl_map_copy(stmt->args[j]->acc.access));
	stmt->args[i]->acc.access = isl_map_coalesce(stmt->args[i]->acc.access);

	pet_expr_free(stmt->args[j]);
	for (k = j; k < stmt->n_arg - 1; ++k)
		stmt->args[k] = stmt->args[k + 1];
	stmt->n_arg--;

	map = isl_set_unwrap(stmt->domain);
	map = isl_map_project_out(map, isl_dim_out, j, 1);
	stmt->domain = isl_map_wrap(map);

	if (!stmt->domain || !stmt->args[i]->acc.access)
		return pet_stmt_free(stmt);

	return stmt;
}

/* Look for any pair of filters that access the same filter variable
 * and that have the same filter value and merge them into a single
 * filter with as filter access relation the union of the filter access
 * relations.
 */
static struct pet_stmt *stmt_merge_filters(struct pet_stmt *stmt)
{
	int i, j;
	isl_space *space_i, *space_j;

	if (!stmt)
		return NULL;
	if (stmt->n_arg <= 1)
		return stmt;

	for (i = 0; i < stmt->n_arg - 1; ++i) {
		if (stmt->args[i]->type != pet_expr_access)
			continue;
		if (pet_expr_is_affine(stmt->args[i]))
			continue;

		space_i = isl_map_get_space(stmt->args[i]->acc.access);
		
		for (j = stmt->n_arg - 1; j > i; --j) {
			int eq;

			if (stmt->args[j]->type != pet_expr_access)
				continue;
			if (pet_expr_is_affine(stmt->args[j]))
				continue;

			space_j = isl_map_get_space(stmt->args[j]->acc.access);

			eq = isl_space_is_equal(space_i, space_j);
			if (eq >= 0 && eq)
				eq = equal_filter_values(stmt->domain, i, j);
			if (eq >= 0 && eq)
				stmt = merge_filter_pair(stmt, i, j);

			isl_space_free(space_j);

			if (eq < 0 || !stmt)
				break;
		}

		isl_space_free(space_i);

		if (j > i || !stmt)
			return pet_stmt_free(stmt);
	}

	return stmt;
}

/* Look for any pair of filters that access the same filter variable
 * and that have the same filter value and merge them into a single
 * filter with as filter access relation the union of the filter access
 * relations.
 */
struct pet_scop *pet_scop_merge_filters(struct pet_scop *scop)
{
	int i;

	if (!scop)
		return NULL;

	for (i = 0; i < scop->n_stmt; ++i) {
		scop->stmts[i] = stmt_merge_filters(scop->stmts[i]);
		if (!scop->stmts[i])
			return pet_scop_free(scop);
	}

	return scop;
}

/* Add all parameters in "expr" to "dim" and return the result.
 */
static __isl_give isl_space *expr_collect_params(struct pet_expr *expr,
	__isl_take isl_space *dim)
{
	int i;

	if (!expr)
		goto error;
	for (i = 0; i < expr->n_arg; ++i)

		dim = expr_collect_params(expr->args[i], dim);

	if (expr->type == pet_expr_access)
		dim = isl_space_align_params(dim,
					    isl_map_get_space(expr->acc.access));

	return dim;
error:
	isl_space_free(dim);
	return pet_expr_free(expr);
}

/* Add all parameters in "stmt" to "dim" and return the result.
 */
static __isl_give isl_space *stmt_collect_params(struct pet_stmt *stmt,
	__isl_take isl_space *dim)
{
	if (!stmt)
		goto error;

	dim = isl_space_align_params(dim, isl_set_get_space(stmt->domain));
	dim = isl_space_align_params(dim, isl_map_get_space(stmt->schedule));
	dim = expr_collect_params(stmt->body, dim);

	return dim;
error:
	isl_space_free(dim);
	return pet_stmt_free(stmt);
}

/* Add all parameters in "array" to "dim" and return the result.
 */
static __isl_give isl_space *array_collect_params(struct pet_array *array,
	__isl_take isl_space *dim)
{
	if (!array)
		goto error;

	dim = isl_space_align_params(dim, isl_set_get_space(array->context));
	dim = isl_space_align_params(dim, isl_set_get_space(array->extent));

	return dim;
error:
	isl_space_free(dim);
	return pet_array_free(array);
}

/* Add all parameters in "scop" to "dim" and return the result.
 */
static __isl_give isl_space *scop_collect_params(struct pet_scop *scop,
	__isl_take isl_space *dim)
{
	int i;

	if (!scop)
		goto error;

	for (i = 0; i < scop->n_array; ++i)
		dim = array_collect_params(scop->arrays[i], dim);

	for (i = 0; i < scop->n_stmt; ++i)
		dim = stmt_collect_params(scop->stmts[i], dim);

	return dim;
error:
	isl_space_free(dim);
	return pet_scop_free(scop);
}

/* Add all parameters in "dim" to all access relations in "expr".
 */
static struct pet_expr *expr_propagate_params(struct pet_expr *expr,
	__isl_take isl_space *dim)
{
	int i;

	if (!expr)
		goto error;

	for (i = 0; i < expr->n_arg; ++i) {
		expr->args[i] =
			expr_propagate_params(expr->args[i],
						isl_space_copy(dim));
		if (!expr->args[i])
			goto error;
	}

	if (expr->type == pet_expr_access) {
		expr->acc.access = isl_map_align_params(expr->acc.access,
							isl_space_copy(dim));
		if (!expr->acc.access)
			goto error;
	}

	isl_space_free(dim);
	return expr;
error:
	isl_space_free(dim);
	return pet_expr_free(expr);
}

/* Add all parameters in "dim" to the domain, schedule and
 * all access relations in "stmt".
 */
static struct pet_stmt *stmt_propagate_params(struct pet_stmt *stmt,
	__isl_take isl_space *dim)
{
	if (!stmt)
		goto error;

	stmt->domain = isl_set_align_params(stmt->domain, isl_space_copy(dim));
	stmt->schedule = isl_map_align_params(stmt->schedule,
						isl_space_copy(dim));
	stmt->body = expr_propagate_params(stmt->body, isl_space_copy(dim));

	if (!stmt->domain || !stmt->schedule || !stmt->body)
		goto error;

	isl_space_free(dim);
	return stmt;
error:
	isl_space_free(dim);
	return pet_stmt_free(stmt);
}

/* Add all parameters in "dim" to "array".
 */
static struct pet_array *array_propagate_params(struct pet_array *array,
	__isl_take isl_space *dim)
{
	if (!array)
		goto error;

	array->context = isl_set_align_params(array->context,
						isl_space_copy(dim));
	array->extent = isl_set_align_params(array->extent,
						isl_space_copy(dim));
	if (array->value_bounds) {
		array->value_bounds = isl_set_align_params(array->value_bounds,
							isl_space_copy(dim));
		if (!array->value_bounds)
			goto error;
	}

	if (!array->context || !array->extent)
		goto error;

	isl_space_free(dim);
	return array;
error:
	isl_space_free(dim);
	return pet_array_free(array);
}

/* Add all parameters in "dim" to "scop".
 */
static struct pet_scop *scop_propagate_params(struct pet_scop *scop,
	__isl_take isl_space *dim)
{
	int i;

	if (!scop)
		goto error;

	for (i = 0; i < scop->n_array; ++i) {
		scop->arrays[i] = array_propagate_params(scop->arrays[i],
							isl_space_copy(dim));
		if (!scop->arrays[i])
			goto error;
	}

	for (i = 0; i < scop->n_stmt; ++i) {
		scop->stmts[i] = stmt_propagate_params(scop->stmts[i],
							isl_space_copy(dim));
		if (!scop->stmts[i])
			goto error;
	}

	isl_space_free(dim);
	return scop;
error:
	isl_space_free(dim);
	return pet_scop_free(scop);
}

/* Update all isl_sets and isl_maps in "scop" such that they all
 * have the same parameters.
 */
struct pet_scop *pet_scop_align_params(struct pet_scop *scop)
{
	isl_space *dim;

	if (!scop)
		return NULL;

	dim = isl_set_get_space(scop->context);
	dim = scop_collect_params(scop, dim);

	scop->context = isl_set_align_params(scop->context, isl_space_copy(dim));
	scop = scop_propagate_params(scop, dim);

	return scop;
}

/* Check if the given access relation accesses a (0D) array that corresponds
 * to one of the parameters in "dim".  If so, replace the array access
 * by an access to the set of integers with as index (and value)
 * that parameter.
 */
static __isl_give isl_map *access_detect_parameter(__isl_take isl_map *access,
	__isl_take isl_space *dim)
{
	isl_id *array_id = NULL;
	int pos = -1;

	if (isl_map_has_tuple_id(access, isl_dim_out)) {
		array_id = isl_map_get_tuple_id(access, isl_dim_out);
		pos = isl_space_find_dim_by_id(dim, isl_dim_param, array_id);
	}
	isl_space_free(dim);

	if (pos < 0) {
		isl_id_free(array_id);
		return access;
	}

	pos = isl_map_find_dim_by_id(access, isl_dim_param, array_id);
	if (pos < 0) {
		access = isl_map_insert_dims(access, isl_dim_param, 0, 1);
		access = isl_map_set_dim_id(access, isl_dim_param, 0, array_id);
		pos = 0;
	} else
		isl_id_free(array_id);

	access = isl_map_insert_dims(access, isl_dim_out, 0, 1);
	access = isl_map_equate(access, isl_dim_param, pos, isl_dim_out, 0);

	return access;
}

/* Replace all accesses to (0D) arrays that correspond to one of the parameters
 * in "dim" by a value equal to the corresponding parameter.
 */
static struct pet_expr *expr_detect_parameter_accesses(struct pet_expr *expr,
	__isl_take isl_space *dim)
{
	int i;

	if (!expr)
		goto error;

	for (i = 0; i < expr->n_arg; ++i) {
		expr->args[i] =
			expr_detect_parameter_accesses(expr->args[i],
						isl_space_copy(dim));
		if (!expr->args[i])
			goto error;
	}

	if (expr->type == pet_expr_access) {
		expr->acc.access = access_detect_parameter(expr->acc.access,
							isl_space_copy(dim));
		if (!expr->acc.access)
			goto error;
	}

	isl_space_free(dim);
	return expr;
error:
	isl_space_free(dim);
	return pet_expr_free(expr);
}

/* Replace all accesses to (0D) arrays that correspond to one of the parameters
 * in "dim" by a value equal to the corresponding parameter.
 */
static struct pet_stmt *stmt_detect_parameter_accesses(struct pet_stmt *stmt,
	__isl_take isl_space *dim)
{
	if (!stmt)
		goto error;

	stmt->body = expr_detect_parameter_accesses(stmt->body,
							isl_space_copy(dim));

	if (!stmt->domain || !stmt->schedule || !stmt->body)
		goto error;

	isl_space_free(dim);
	return stmt;
error:
	isl_space_free(dim);
	return pet_stmt_free(stmt);
}

/* Replace all accesses to (0D) arrays that correspond to one of the parameters
 * in "dim" by a value equal to the corresponding parameter.
 */
static struct pet_scop *scop_detect_parameter_accesses(struct pet_scop *scop,
	__isl_take isl_space *dim)
{
	int i;

	if (!scop)
		goto error;

	for (i = 0; i < scop->n_stmt; ++i) {
		scop->stmts[i] = stmt_detect_parameter_accesses(scop->stmts[i],
							isl_space_copy(dim));
		if (!scop->stmts[i])
			goto error;
	}

	isl_space_free(dim);
	return scop;
error:
	isl_space_free(dim);
	return pet_scop_free(scop);
}

/* Replace all accesses to (0D) arrays that correspond to any of
 * the parameters used in "scop" by a value equal
 * to the corresponding parameter.
 */
struct pet_scop *pet_scop_detect_parameter_accesses(struct pet_scop *scop)
{
	isl_space *dim;

	if (!scop)
		return NULL;

	dim = isl_set_get_space(scop->context);
	dim = scop_collect_params(scop, dim);

	scop = scop_detect_parameter_accesses(scop, dim);

	return scop;
}

/* Add all read access relations (if "read" is set) and/or all write
 * access relations (if "write" is set) to "accesses" and return the result.
 */
static __isl_give isl_union_map *expr_collect_accesses(struct pet_expr *expr,
	int read, int write, __isl_take isl_union_map *accesses)
{
	int i;
	isl_id *id;
	isl_space *dim;

	if (!expr)
		return NULL;

	for (i = 0; i < expr->n_arg; ++i)
		accesses = expr_collect_accesses(expr->args[i],
						 read, write, accesses);

	if (expr->type == pet_expr_access &&
	    isl_map_has_tuple_id(expr->acc.access, isl_dim_out) &&
	    ((read && expr->acc.read) || (write && expr->acc.write)))
		accesses = isl_union_map_add_map(accesses,
						isl_map_copy(expr->acc.access));

	return accesses;
}

/* Collect and return all read access relations (if "read" is set)
 * and/or all write * access relations (if "write" is set) in "stmt".
 */
static __isl_give isl_union_map *stmt_collect_accesses(struct pet_stmt *stmt,
	int read, int write, __isl_take isl_space *dim)
{
	isl_union_map *accesses;

	if (!stmt)
		return NULL;

	accesses = isl_union_map_empty(dim);
	accesses = expr_collect_accesses(stmt->body, read, write, accesses);
	accesses = isl_union_map_intersect_domain(accesses,
			isl_union_set_from_set(isl_set_copy(stmt->domain)));

	return accesses;
}

/* Collect and return all read access relations (if "read" is set)
 * and/or all write * access relations (if "write" is set) in "scop".
 */
static __isl_give isl_union_map *scop_collect_accesses(struct pet_scop *scop,
	int read, int write)
{
	int i;
	isl_union_map *accesses;

	if (!scop)
		return NULL;

	accesses = isl_union_map_empty(isl_set_get_space(scop->context));

	for (i = 0; i < scop->n_stmt; ++i) {
		isl_union_map *accesses_i;
		isl_space *dim = isl_set_get_space(scop->context);
		accesses_i = stmt_collect_accesses(scop->stmts[i],
						   read, write, dim);
		accesses = isl_union_map_union(accesses, accesses_i);
	}

	return accesses;
}

__isl_give isl_union_map *pet_scop_collect_reads(struct pet_scop *scop)
{
	return scop_collect_accesses(scop, 1, 0);
}

__isl_give isl_union_map *pet_scop_collect_writes(struct pet_scop *scop)
{
	return scop_collect_accesses(scop, 0, 1);
}

/* Collect and return the union of iteration domains in "scop".
 */
__isl_give isl_union_set *pet_scop_collect_domains(struct pet_scop *scop)
{
	int i;
	isl_set *domain_i;
	isl_union_set *domain;

	if (!scop)
		return NULL;

	domain = isl_union_set_empty(isl_set_get_space(scop->context));

	for (i = 0; i < scop->n_stmt; ++i) {
		domain_i = isl_set_copy(scop->stmts[i]->domain);
		domain = isl_union_set_add_set(domain, domain_i);
	}

	return domain;
}

/* Collect and return the schedules of the statements in "scop".
 * The range is normalized to the maximal number of scheduling
 * dimensions.
 */
__isl_give isl_union_map *pet_scop_collect_schedule(struct pet_scop *scop)
{
	int i, j;
	isl_map *schedule_i;
	isl_union_map *schedule;
	int depth, max_depth = 0;

	if (!scop)
		return NULL;

	schedule = isl_union_map_empty(isl_set_get_space(scop->context));

	for (i = 0; i < scop->n_stmt; ++i) {
		depth = isl_map_dim(scop->stmts[i]->schedule, isl_dim_out);
		if (depth > max_depth)
			max_depth = depth;
	}

	for (i = 0; i < scop->n_stmt; ++i) {
		schedule_i = isl_map_copy(scop->stmts[i]->schedule);
		depth = isl_map_dim(schedule_i, isl_dim_out);
		schedule_i = isl_map_add_dims(schedule_i, isl_dim_out,
						max_depth - depth);
		for (j = depth; j < max_depth; ++j)
			schedule_i = isl_map_fix_si(schedule_i,
							isl_dim_out, j, 0);
		schedule = isl_union_map_add_map(schedule, schedule_i);
	}

	return schedule;
}

/* Does expression "expr" write to "id"?
 */
static int expr_writes(struct pet_expr *expr, __isl_keep isl_id *id)
{
	int i;
	isl_id *write_id;

	for (i = 0; i < expr->n_arg; ++i) {
		int writes = expr_writes(expr->args[i], id);
		if (writes < 0 || writes)
			return writes;
	}

	if (expr->type != pet_expr_access)
		return 0;
	if (!expr->acc.write)
		return 0;
	if (!isl_map_has_tuple_id(expr->acc.access, isl_dim_out))
		return 0;

	write_id = isl_map_get_tuple_id(expr->acc.access, isl_dim_out);
	isl_id_free(write_id);

	if (!write_id)
		return -1;

	return write_id == id;
}

/* Does statement "stmt" write to "id"?
 */
static int stmt_writes(struct pet_stmt *stmt, __isl_keep isl_id *id)
{
	return expr_writes(stmt->body, id);
}

/* Is there any write access in "scop" that accesses "id"?
 */
int pet_scop_writes(struct pet_scop *scop, __isl_keep isl_id *id)
{
	int i;

	if (!scop)
		return -1;

	for (i = 0; i < scop->n_stmt; ++i) {
		int writes = stmt_writes(scop->stmts[i], id);
		if (writes < 0 || writes)
			return writes;
	}

	return 0;
}

/* Reset the user pointer on all parameter ids in "set".
 */
static __isl_give isl_set *set_anonymize(__isl_take isl_set *set)
{
	int i, n;

	n = isl_set_dim(set, isl_dim_param);
	for (i = 0; i < n; ++i) {
		isl_id *id = isl_set_get_dim_id(set, isl_dim_param, i);
		const char *name = isl_id_get_name(id);
		set = isl_set_set_dim_name(set, isl_dim_param, i, name);
		isl_id_free(id);
	}

	return set;
}

/* Reset the user pointer on all parameter ids in "map".
 */
static __isl_give isl_map *map_anonymize(__isl_take isl_map *map)
{
	int i, n;

	n = isl_map_dim(map, isl_dim_param);
	for (i = 0; i < n; ++i) {
		isl_id *id = isl_map_get_dim_id(map, isl_dim_param, i);
		const char *name = isl_id_get_name(id);
		map = isl_map_set_dim_name(map, isl_dim_param, i, name);
		isl_id_free(id);
	}

	return map;
}

/* Reset the user pointer on all parameter ids in "array".
 */
static struct pet_array *array_anonymize(struct pet_array *array)
{
	if (!array)
		return NULL;

	array->context = set_anonymize(array->context);
	array->extent = set_anonymize(array->extent);
	if (!array->context || !array->extent)
		return pet_array_free(array);

	return array;
}

/* Reset the user pointer on all parameter ids in "access".
 */
static __isl_give isl_map *access_anonymize(__isl_take isl_map *access,
	void *user)
{
	access = map_anonymize(access);

	return access;
}

/* Reset the user pointer on all parameter ids in "stmt".
 */
static struct pet_stmt *stmt_anonymize(struct pet_stmt *stmt)
{
	int i;
	isl_space *space;
	isl_set *domain;

	if (!stmt)
		return NULL;

	stmt->domain = set_anonymize(stmt->domain);
	stmt->schedule = map_anonymize(stmt->schedule);
	if (!stmt->domain || !stmt->schedule)
		return pet_stmt_free(stmt);

	for (i = 0; i < stmt->n_arg; ++i) {
		stmt->args[i] = pet_expr_foreach_access(stmt->args[i],
						    &access_anonymize, NULL);
		if (!stmt->args[i])
			return pet_stmt_free(stmt);
	}

	stmt->body = pet_expr_foreach_access(stmt->body,
						    &access_anonymize, NULL);
	if (!stmt->body)
		return pet_stmt_free(stmt);

	return stmt;
}

/* Reset the user pointer on all parameter ids in "scop".
 */
struct pet_scop *pet_scop_anonymize(struct pet_scop *scop)
{
	int i;

	if (!scop)
		return NULL;

	scop->context = set_anonymize(scop->context);
	scop->context_value = set_anonymize(scop->context_value);
	if (!scop->context || !scop->context_value)
		return pet_scop_free(scop);

	for (i = 0; i < scop->n_array; ++i) {
		scop->arrays[i] = array_anonymize(scop->arrays[i]);
		if (!scop->arrays[i])
			return pet_scop_free(scop);
	}

	for (i = 0; i < scop->n_stmt; ++i) {
		scop->stmts[i] = stmt_anonymize(scop->stmts[i]);
		if (!scop->stmts[i])
			return pet_scop_free(scop);
	}

	return scop;
}

/* Given a set "domain", return a wrapped relation with the given set
 * as domain and a range of dimension "n_arg", where each coordinate
 * is either unbounded or, if the corresponding element of args is of
 * type pet_expr_access, bounded by the bounds specified by "value_bounds".
 */
static __isl_give isl_set *apply_value_bounds(__isl_take isl_set *domain,
	unsigned n_arg, struct pet_expr **args,
	__isl_keep isl_union_map *value_bounds)
{
	int i;
	isl_map *map;
	isl_space *space;
	isl_ctx *ctx = isl_set_get_ctx(domain);

	map = isl_map_from_domain(domain);
	space = isl_map_get_space(map);
	space = isl_space_add_dims(space, isl_dim_out, 1);

	for (i = 0; i < n_arg; ++i) {
		isl_map *map_i;
		struct pet_expr *arg = args[i];
		isl_id *id;
		isl_space *space2;

		map_i = isl_map_universe(isl_space_copy(space));
		if (arg->type == pet_expr_access) {
			isl_map *vb;
			id = isl_map_get_tuple_id(arg->acc.access, isl_dim_out);
			space2 = isl_space_alloc(ctx, 0, 0, 1);
			space2 = isl_space_set_tuple_id(space2, isl_dim_in, id);
			vb = isl_union_map_extract_map(value_bounds, space2);
			if (!isl_map_plain_is_empty(vb))
				map_i = isl_map_intersect_range(map_i,
							    isl_map_range(vb));
			else
				isl_map_free(vb);
		}
		map = isl_map_flat_range_product(map, map_i);
	}
	isl_space_free(space);

	return isl_map_wrap(map);
}

/* Data used in access_gist() callback.
 */
struct pet_access_gist_data {
	isl_set *domain;
	isl_union_map *value_bounds;
};

/* Given an expression "expr" of type pet_expr_access, compute
 * the gist of the associated access relation with respect to
 * data->domain and the bounds on the values of the arguments
 * of the expression.
 */
static struct pet_expr *access_gist(struct pet_expr *expr, void *user)
{
	struct pet_access_gist_data *data = user;
	isl_set *domain;

	domain = isl_set_copy(data->domain);
	if (expr->n_arg > 0)
		domain = apply_value_bounds(domain, expr->n_arg, expr->args,
						data->value_bounds);

	expr->acc.access = isl_map_gist_domain(expr->acc.access, domain);
	if (!expr->acc.access)
		return pet_expr_free(expr);

	return expr;
}

/* Compute the gist of the iteration domain and all access relations
 * of "stmt" based on the constraints on the parameters specified by "context"
 * and the constraints on the values of nested accesses specified
 * by "value_bounds".
 */
static struct pet_stmt *stmt_gist(struct pet_stmt *stmt,
	__isl_keep isl_set *context, __isl_keep isl_union_map *value_bounds)
{
	int i;
	isl_space *space;
	isl_set *domain;
	struct pet_access_gist_data data;

	if (!stmt)
		return NULL;

	data.domain = isl_set_copy(stmt->domain);
	data.value_bounds = value_bounds;
	if (stmt->n_arg > 0)
		data.domain = isl_map_domain(isl_set_unwrap(data.domain));

	data.domain = isl_set_intersect_params(data.domain,
						isl_set_copy(context));

	for (i = 0; i < stmt->n_arg; ++i) {
		stmt->args[i] = pet_expr_foreach_access_expr(stmt->args[i],
							&access_gist, &data);
		if (!stmt->args[i])
			goto error;
	}

	stmt->body = pet_expr_foreach_access_expr(stmt->body,
							&access_gist, &data);
	if (!stmt->body)
		goto error;

	isl_set_free(data.domain);

	space = isl_set_get_space(stmt->domain);
	if (isl_space_is_wrapping(space))
		space = isl_space_domain(isl_space_unwrap(space));
	domain = isl_set_universe(space);
	domain = isl_set_intersect_params(domain, isl_set_copy(context));
	if (stmt->n_arg > 0)
		domain = apply_value_bounds(domain, stmt->n_arg, stmt->args,
						value_bounds);
	stmt->domain = isl_set_gist(stmt->domain, domain);
	if (!stmt->domain)
		return pet_stmt_free(stmt);

	return stmt;
error:
	isl_set_free(data.domain);
	return pet_stmt_free(stmt);
}

/* Compute the gist of the extent of the array
 * based on the constraints on the parameters specified by "context".
 */
static struct pet_array *array_gist(struct pet_array *array,
	__isl_keep isl_set *context)
{
	if (!array)
		return NULL;

	array->extent = isl_set_gist_params(array->extent,
						isl_set_copy(context));
	if (!array->extent)
		return pet_array_free(array);

	return array;
}

/* Compute the gist of all sets and relations in "scop"
 * based on the constraints on the parameters specified by "scop->context"
 * and the constraints on the values of nested accesses specified
 * by "value_bounds".
 */
struct pet_scop *pet_scop_gist(struct pet_scop *scop,
	__isl_keep isl_union_map *value_bounds)
{
	int i;

	if (!scop)
		return NULL;

	scop->context = isl_set_coalesce(scop->context);
	if (!scop->context)
		return pet_scop_free(scop);

	for (i = 0; i < scop->n_array; ++i) {
		scop->arrays[i] = array_gist(scop->arrays[i], scop->context);
		if (!scop->arrays[i])
			return pet_scop_free(scop);
	}

	for (i = 0; i < scop->n_stmt; ++i) {
		scop->stmts[i] = stmt_gist(scop->stmts[i], scop->context,
					    value_bounds);
		if (!scop->stmts[i])
			return pet_scop_free(scop);
	}

	return scop;
}

/* Intersect the context of "scop" with "context".
 * To ensure that we don't introduce any unnamed parameters in
 * the context of "scop", we first remove the unnamed parameters
 * from "context".
 */
struct pet_scop *pet_scop_restrict_context(struct pet_scop *scop,
	__isl_take isl_set *context)
{
	if (!scop)
		goto error;

	context = set_project_out_unnamed_params(context);
	scop->context = isl_set_intersect(scop->context, context);
	if (!scop->context)
		return pet_scop_free(scop);

	return scop;
error:
	isl_set_free(context);
	return pet_scop_free(scop);
}

/* Drop the current context of "scop".  That is, replace the context
 * by a universal set.
 */
struct pet_scop *pet_scop_reset_context(struct pet_scop *scop)
{
	isl_space *space;

	if (!scop)
		return NULL;

	space = isl_set_get_space(scop->context);
	isl_set_free(scop->context);
	scop->context = isl_set_universe(space);
	if (!scop->context)
		return pet_scop_free(scop);

	return scop;
}
