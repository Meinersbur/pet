/*
 * Copyright 2011      Leiden University. All rights reserved.
 * Copyright 2012-2014 Ecole Normale Superieure. All rights reserved.
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

#include <string.h>

#include "expr.h"
#include "filter.h"
#include "value_bounds.h"

#define ARRAY_SIZE(array) (sizeof(array)/sizeof(*array))

static char *type_str[] = {
	[pet_expr_access] = "access",
	[pet_expr_call] = "call",
	[pet_expr_cast] = "cast",
	[pet_expr_double] = "double",
	[pet_expr_int] = "int",
	[pet_expr_op] = "op",
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
	[pet_op_shl] = "<<",
	[pet_op_shr] = ">>",
	[pet_op_eq] = "==",
	[pet_op_ne] = "!=",
	[pet_op_le] = "<=",
	[pet_op_ge] = ">=",
	[pet_op_lt] = "<",
	[pet_op_gt] = ">",
	[pet_op_minus] = "-",
	[pet_op_post_inc] = "++",
	[pet_op_post_dec] = "--",
	[pet_op_pre_inc] = "++",
	[pet_op_pre_dec] = "--",
	[pet_op_address_of] = "&",
	[pet_op_and] = "&",
	[pet_op_xor] = "^",
	[pet_op_or] = "|",
	[pet_op_not] = "~",
	[pet_op_land] = "&&",
	[pet_op_lor] = "||",
	[pet_op_lnot] = "!",
	[pet_op_cond] = "?:",
	[pet_op_assume] = "assume",
	[pet_op_kill] = "kill"
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

/* Construct an access pet_expr from an access relation and an index expression.
 * By default, it is considered to be a read access.
 */
struct pet_expr *pet_expr_from_access_and_index( __isl_take isl_map *access,
	__isl_take isl_multi_pw_aff *index)
{
	isl_ctx *ctx = isl_map_get_ctx(access);
	struct pet_expr *expr;

	if (!index || !access)
		goto error;
	expr = isl_calloc_type(ctx, struct pet_expr);
	if (!expr)
		goto error;

	expr->type = pet_expr_access;
	expr->acc.access = access;
	expr->acc.index = index;
	expr->acc.read = 1;
	expr->acc.write = 0;

	return expr;
error:
	isl_map_free(access);
	isl_multi_pw_aff_free(index);
	return NULL;
}

/* Construct an access pet_expr from an index expression.
 * By default, the access is considered to be a read access.
 */
struct pet_expr *pet_expr_from_index(__isl_take isl_multi_pw_aff *index)
{
	isl_map *access;

	access = isl_map_from_multi_pw_aff(isl_multi_pw_aff_copy(index));
	return pet_expr_from_access_and_index(access, index);
}

/* Extend the range of "access" with "n" dimensions, retaining
 * the tuple identifier on this range.
 *
 * If "access" represents a member access, then extend the range
 * of the member.
 */
static __isl_give isl_map *extend_range(__isl_take isl_map *access, int n)
{
	isl_id *id;

	id = isl_map_get_tuple_id(access, isl_dim_out);

	if (!isl_map_range_is_wrapping(access)) {
		access = isl_map_add_dims(access, isl_dim_out, n);
	} else {
		isl_map *domain;

		domain = isl_map_copy(access);
		domain = isl_map_range_factor_domain(domain);
		access = isl_map_range_factor_range(access);
		access = extend_range(access, n);
		access = isl_map_range_product(domain, access);
	}

	access = isl_map_set_tuple_id(access, isl_dim_out, id);

	return access;
}

/* Construct an access pet_expr from an index expression and
 * the depth of the accessed array.
 * By default, the access is considered to be a read access.
 *
 * If the number of indices is smaller than the depth of the array,
 * then we assume that all elements of the remaining dimensions
 * are accessed.
 */
struct pet_expr *pet_expr_from_index_and_depth(
	__isl_take isl_multi_pw_aff *index, int depth)
{
	isl_map *access;
	int dim;

	access = isl_map_from_multi_pw_aff(isl_multi_pw_aff_copy(index));
	if (!access)
		goto error;
	dim = isl_map_dim(access, isl_dim_out);
	if (dim > depth)
		isl_die(isl_map_get_ctx(access), isl_error_internal,
			"number of indices greater than depth",
			access = isl_map_free(access));
	if (dim == depth)
		return pet_expr_from_access_and_index(access, index);

	access = extend_range(access, depth - dim);

	return pet_expr_from_access_and_index(access, index);
error:
	isl_multi_pw_aff_free(index);
	return NULL;
}

/* Construct a pet_expr that kills the elements specified by
 * the index expression "index" and the access relation "access".
 */
struct pet_expr *pet_expr_kill_from_access_and_index(__isl_take isl_map *access,
	__isl_take isl_multi_pw_aff *index)
{
	isl_ctx *ctx;
	struct pet_expr *expr;

	if (!access || !index)
		goto error;

	ctx = isl_multi_pw_aff_get_ctx(index);
	expr = pet_expr_from_access_and_index(access, index);
	if (!expr)
		return NULL;
	expr->acc.read = 0;
	return pet_expr_new_unary(ctx, pet_op_kill, expr);
error:
	isl_map_free(access);
	isl_multi_pw_aff_free(index);
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

	expr->type = pet_expr_op;
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

	expr->type = pet_expr_op;
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

	expr->type = pet_expr_op;
	expr->op = pet_op_cond;
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

/* Construct a pet_expr that represents the cast of "arg" to "type_name".
 */
struct pet_expr *pet_expr_new_cast(isl_ctx *ctx, const char *type_name,
	struct pet_expr *arg)
{
	struct pet_expr *expr;

	if (!arg)
		return NULL;

	expr = isl_alloc_type(ctx, struct pet_expr);
	if (!expr)
		goto error;

	expr->type = pet_expr_cast;
	expr->n_arg = 1;
	expr->type_name = strdup(type_name);
	expr->args = isl_calloc_array(ctx, struct pet_expr *, 1);
	if (!expr->type_name || !expr->args)
		goto error;

	expr->args[0] = arg;

	return expr;
error:
	pet_expr_free(arg);
	pet_expr_free(expr);
	return NULL;
}

/* Construct a pet_expr that represents the double "d".
 */
struct pet_expr *pet_expr_new_double(isl_ctx *ctx, double val, const char *s)
{
	struct pet_expr *expr;

	expr = isl_calloc_type(ctx, struct pet_expr);
	if (!expr)
		return NULL;

	expr->type = pet_expr_double;
	expr->d.val = val;
	expr->d.s = strdup(s);
	if (!expr->d.s)
		return pet_expr_free(expr);

	return expr;
}

/* Construct a pet_expr that represents the integer value "v".
 */
struct pet_expr *pet_expr_new_int(__isl_take isl_val *v)
{
	isl_ctx *ctx;
	struct pet_expr *expr;

	if (!v)
		return NULL;

	ctx = isl_val_get_ctx(v);
	expr = isl_calloc_type(ctx, struct pet_expr);
	if (!expr)
		goto error;

	expr->type = pet_expr_int;
	expr->i = v;

	return expr;
error:
	isl_val_free(v);
	return NULL;
}

struct pet_expr *pet_expr_free(struct pet_expr *expr)
{
	int i;

	if (!expr)
		return NULL;

	for (i = 0; i < expr->n_arg; ++i)
		pet_expr_free(expr->args[i]);
	free(expr->args);

	switch (expr->type) {
	case pet_expr_access:
		isl_id_free(expr->acc.ref_id);
		isl_map_free(expr->acc.access);
		isl_multi_pw_aff_free(expr->acc.index);
		break;
	case pet_expr_call:
		free(expr->name);
		break;
	case pet_expr_cast:
		free(expr->type_name);
		break;
	case pet_expr_double:
		free(expr->d.s);
		break;
	case pet_expr_int:
		isl_val_free(expr->i);
		break;
	case pet_expr_op:
		break;
	}

	free(expr);
	return NULL;
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

/* Does "expr" represent an access to a scalar, i.e., zero-dimensional array?
 */
int pet_expr_is_scalar_access(struct pet_expr *expr)
{
	if (!expr)
		return -1;
	if (expr->type != pet_expr_access)
		return 0;

	return isl_map_dim(expr->acc.access, isl_dim_out) == 0;
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
		if (strcmp(expr1->d.s, expr2->d.s))
			return 0;
		if (expr1->d.val != expr2->d.val)
			return 0;
		break;
	case pet_expr_int:
		if (!isl_val_eq(expr1->i, expr2->i))
			return 0;
		break;
	case pet_expr_access:
		if (expr1->acc.read != expr2->acc.read)
			return 0;
		if (expr1->acc.write != expr2->acc.write)
			return 0;
		if (expr1->acc.ref_id != expr2->acc.ref_id)
			return 0;
		if (!expr1->acc.access || !expr2->acc.access)
			return 0;
		if (!isl_map_is_equal(expr1->acc.access, expr2->acc.access))
			return 0;
		if (!expr1->acc.index || !expr2->acc.index)
			return 0;
		if (!isl_multi_pw_aff_plain_is_equal(expr1->acc.index,
							expr2->acc.index))
			return 0;
		break;
	case pet_expr_op:
		if (expr1->op != expr2->op)
			return 0;
		break;
	case pet_expr_call:
		if (strcmp(expr1->name, expr2->name))
			return 0;
		break;
	case pet_expr_cast:
		if (strcmp(expr1->type_name, expr2->type_name))
			return 0;
		break;
	}

	return 1;
}

/* Return the identifier of the array accessed by "expr".
 *
 * If "expr" represents a member access, then return the identifier
 * of the outer structure array.
 */
__isl_give isl_id *pet_expr_access_get_id(struct pet_expr *expr)
{
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		return NULL;

	if (isl_map_range_is_wrapping(expr->acc.access)) {
		isl_space *space;
		isl_id *id;

		space = isl_map_get_space(expr->acc.access);
		space = isl_space_range(space);
		while (space && isl_space_is_wrapping(space))
			space = isl_space_domain(isl_space_unwrap(space));
		id = isl_space_get_tuple_id(space, isl_dim_set);
		isl_space_free(space);

		return id;
	}

	return isl_map_get_tuple_id(expr->acc.access, isl_dim_out);
}

/* Return the parameter space of "expr".
 */
__isl_give isl_space *pet_expr_access_get_parameter_space(struct pet_expr *expr)
{
	isl_space *space;

	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		return NULL;

	space = isl_multi_pw_aff_get_space(expr->acc.index);
	space = isl_space_params(space);

	return space;
}

/* Return the space of the data accessed by "expr".
 */
__isl_give isl_space *pet_expr_access_get_data_space(struct pet_expr *expr)
{
	isl_space *space;

	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		return NULL;

	space = isl_multi_pw_aff_get_space(expr->acc.index);
	space = isl_space_range(space);

	return space;
}

/* Modify all expressions of type pet_expr_access in "expr"
 * by calling "fn" on them.
 */
struct pet_expr *pet_expr_map_access(struct pet_expr *expr,
	struct pet_expr *(*fn)(struct pet_expr *expr, void *user),
	void *user)
{
	int i;

	if (!expr)
		return NULL;

	for (i = 0; i < expr->n_arg; ++i) {
		expr->args[i] = pet_expr_map_access(expr->args[i], fn, user);
		if (!expr->args[i])
			return pet_expr_free(expr);
	}

	if (expr->type == pet_expr_access)
		expr = fn(expr, user);

	return expr;
}

/* Call "fn" on each of the subexpressions of "expr" of type pet_expr_access.
 *
 * Return -1 on error (where fn return a negative value is treated as an error).
 * Otherwise return 0.
 */
int pet_expr_foreach_access_expr(struct pet_expr *expr,
	int (*fn)(struct pet_expr *expr, void *user), void *user)
{
	int i;

	if (!expr)
		return -1;

	for (i = 0; i < expr->n_arg; ++i)
		if (pet_expr_foreach_access_expr(expr->args[i], fn, user) < 0)
			return -1;

	if (expr->type == pet_expr_access)
		return fn(expr, user);

	return 0;
}

/* Internal data structure for pet_expr_writes.
 * "id" is the identifier that we are looking for.
 * "found" is set if we have found the identifier being written to.
 */
struct pet_expr_writes_data {
	isl_id *id;
	int found;
};

/* Given an access expression, check if it writes to data->id.
 * If so, set data->found and abort the search.
 */
static int writes(struct pet_expr *expr, void *user)
{
	struct pet_expr_writes_data *data = user;
	isl_id *write_id;

	if (!expr->acc.write)
		return 0;
	if (pet_expr_is_affine(expr))
		return 0;

	write_id = pet_expr_access_get_id(expr);
	isl_id_free(write_id);

	if (!write_id)
		return -1;

	if (write_id != data->id)
		return 0;

	data->found = 1;
	return -1;
}

/* Does expression "expr" write to "id"?
 */
int pet_expr_writes(struct pet_expr *expr, __isl_keep isl_id *id)
{
	struct pet_expr_writes_data data;

	data.id = id;
	data.found = 0;
	if (pet_expr_foreach_access_expr(expr, &writes, &data) < 0 &&
	    !data.found)
		return -1;

	return data.found;
}

/* Align the parameters of expr->acc.index and expr->acc.access.
 */
struct pet_expr *pet_expr_access_align_params(struct pet_expr *expr)
{
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		return pet_expr_free(expr);

	expr->acc.access = isl_map_align_params(expr->acc.access,
				isl_multi_pw_aff_get_space(expr->acc.index));
	expr->acc.index = isl_multi_pw_aff_align_params(expr->acc.index,
				isl_map_get_space(expr->acc.access));
	if (!expr->acc.access || !expr->acc.index)
		return pet_expr_free(expr);

	return expr;
}

/* Add extra conditions on the parameters to all access relations in "expr".
 *
 * The conditions are not added to the index expression.  Instead, they
 * are used to try and simplify the index expression.
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
		expr->acc.index = isl_multi_pw_aff_gist_params(
					expr->acc.index, isl_set_copy(cond));
		if (!expr->acc.access || !expr->acc.index)
			goto error;
	}

	isl_set_free(cond);
	return expr;
error:
	isl_set_free(cond);
	return pet_expr_free(expr);
}

/* Modify the access relation and index expression
 * of the given access expression
 * based on the given iteration space transformation.
 * In particular, precompose the access relation and index expression
 * with the update function.
 *
 * If the access has any arguments then the domain of the access relation
 * is a wrapped mapping from the iteration space to the space of
 * argument values.  We only need to change the domain of this wrapped
 * mapping, so we extend the input transformation with an identity mapping
 * on the space of argument values.
 */
struct pet_expr *pet_expr_access_update_domain(struct pet_expr *expr,
	__isl_keep isl_multi_pw_aff *update)
{
	isl_space *space;

	update = isl_multi_pw_aff_copy(update);

	space = isl_map_get_space(expr->acc.access);
	space = isl_space_domain(space);
	if (!isl_space_is_wrapping(space))
		isl_space_free(space);
	else {
		isl_multi_pw_aff *id;
		space = isl_space_unwrap(space);
		space = isl_space_range(space);
		space = isl_space_map_from_set(space);
		id = isl_multi_pw_aff_identity(space);
		update = isl_multi_pw_aff_product(update, id);
	}

	expr->acc.access = isl_map_preimage_domain_multi_pw_aff(
					    expr->acc.access,
					    isl_multi_pw_aff_copy(update));
	expr->acc.index = isl_multi_pw_aff_pullback_multi_pw_aff(
					    expr->acc.index, update);
	if (!expr->acc.access || !expr->acc.index)
		return pet_expr_free(expr);

	return expr;
}

static struct pet_expr *update_domain(struct pet_expr *expr, void *user)
{
	isl_multi_pw_aff *update = user;

	return pet_expr_access_update_domain(expr, update);
}

/* Modify all access relations in "expr" by precomposing them with
 * the given iteration space transformation.
 */
struct pet_expr *pet_expr_update_domain(struct pet_expr *expr,
	__isl_take isl_multi_pw_aff *update)
{
	expr = pet_expr_map_access(expr, &update_domain, update);
	isl_multi_pw_aff_free(update);
	return expr;
}

/* Add all parameters in "space" to the access relation and index expression
 * of "expr".
 */
static struct pet_expr *align_params(struct pet_expr *expr, void *user)
{
	isl_space *space = user;

	expr->acc.access = isl_map_align_params(expr->acc.access,
						isl_space_copy(space));
	expr->acc.index = isl_multi_pw_aff_align_params(expr->acc.index,
						isl_space_copy(space));
	if (!expr->acc.access || !expr->acc.index)
		return pet_expr_free(expr);

	return expr;
}

/* Add all parameters in "space" to all access relations and index expressions
 * in "expr".
 */
struct pet_expr *pet_expr_align_params(struct pet_expr *expr,
	__isl_take isl_space *space)
{
	expr = pet_expr_map_access(expr, &align_params, space);
	isl_space_free(space);
	return expr;
}

/* Insert an argument expression corresponding to "test" in front
 * of the list of arguments described by *n_arg and *args.
 */
static struct pet_expr *insert_access_arg(struct pet_expr *expr,
	__isl_keep isl_multi_pw_aff *test)
{
	int i;
	isl_ctx *ctx = isl_multi_pw_aff_get_ctx(test);

	if (!test)
		return pet_expr_free(expr);

	if (!expr->args) {
		expr->args = isl_calloc_array(ctx, struct pet_expr *, 1);
		if (!expr->args)
			return pet_expr_free(expr);
	} else {
		struct pet_expr **ext;
		ext = isl_calloc_array(ctx, struct pet_expr *, 1 + expr->n_arg);
		if (!ext)
			return pet_expr_free(expr);
		for (i = 0; i < expr->n_arg; ++i)
			ext[1 + i] = expr->args[i];
		free(expr->args);
		expr->args = ext;
	}
	expr->n_arg++;
	expr->args[0] = pet_expr_from_index(isl_multi_pw_aff_copy(test));
	if (!expr->args[0])
		return pet_expr_free(expr);

	return expr;
}

/* Make the expression "expr" depend on the value of "test"
 * being equal to "satisfied".
 *
 * If "test" is an affine expression, we simply add the conditions
 * on the expression having the value "satisfied" to all access relations
 * and index expressions.
 *
 * Otherwise, we add a filter to "expr" (which is then assumed to be
 * an access expression) corresponding to "test" being equal to "satisfied".
 */
struct pet_expr *pet_expr_filter(struct pet_expr *expr,
	__isl_take isl_multi_pw_aff *test, int satisfied)
{
	isl_id *id;
	isl_ctx *ctx;
	isl_space *space;
	isl_pw_multi_aff *pma;

	if (!expr || !test)
		goto error;

	if (!isl_multi_pw_aff_has_tuple_id(test, isl_dim_out)) {
		isl_pw_aff *pa;
		isl_set *cond;

		pa = isl_multi_pw_aff_get_pw_aff(test, 0);
		isl_multi_pw_aff_free(test);
		if (satisfied)
			cond = isl_pw_aff_non_zero_set(pa);
		else
			cond = isl_pw_aff_zero_set(pa);
		return pet_expr_restrict(expr, isl_set_params(cond));
	}

	ctx = isl_multi_pw_aff_get_ctx(test);
	if (expr->type != pet_expr_access)
		isl_die(ctx, isl_error_invalid,
			"can only filter access expressions", goto error);

	space = isl_space_domain(isl_map_get_space(expr->acc.access));
	id = isl_multi_pw_aff_get_tuple_id(test, isl_dim_out);
	pma = pet_filter_insert_pma(space, id, satisfied);

	expr->acc.access = isl_map_preimage_domain_pw_multi_aff(
						expr->acc.access,
						isl_pw_multi_aff_copy(pma));
	expr->acc.index = isl_multi_pw_aff_pullback_pw_multi_aff(
							expr->acc.index, pma);
	if (!expr->acc.access || !expr->acc.index)
		goto error;

	expr = insert_access_arg(expr, test);

	isl_multi_pw_aff_free(test);
	return expr;
error:
	isl_multi_pw_aff_free(test);
	return pet_expr_free(expr);
}

/* Check if the given index expression accesses a (0D) array that corresponds
 * to one of the parameters in "space".  If so, replace the array access
 * by an access to the set of integers with as index (and value)
 * that parameter.
 */
static __isl_give isl_multi_pw_aff *index_detect_parameter(
	__isl_take isl_multi_pw_aff *index, __isl_take isl_space *space)
{
	isl_local_space *ls;
	isl_id *array_id = NULL;
	isl_aff *aff;
	int pos = -1;

	if (isl_multi_pw_aff_has_tuple_id(index, isl_dim_out)) {
		array_id = isl_multi_pw_aff_get_tuple_id(index, isl_dim_out);
		pos = isl_space_find_dim_by_id(space, isl_dim_param, array_id);
	}
	isl_space_free(space);

	if (pos < 0) {
		isl_id_free(array_id);
		return index;
	}

	space = isl_multi_pw_aff_get_domain_space(index);
	isl_multi_pw_aff_free(index);

	pos = isl_space_find_dim_by_id(space, isl_dim_param, array_id);
	if (pos < 0) {
		space = isl_space_insert_dims(space, isl_dim_param, 0, 1);
		space = isl_space_set_dim_id(space, isl_dim_param, 0, array_id);
		pos = 0;
	} else
		isl_id_free(array_id);

	ls = isl_local_space_from_space(space);
	aff = isl_aff_var_on_domain(ls, isl_dim_param, pos);
	index = isl_multi_pw_aff_from_pw_aff(isl_pw_aff_from_aff(aff));

	return index;
}

/* Check if the given access relation accesses a (0D) array that corresponds
 * to one of the parameters in "space".  If so, replace the array access
 * by an access to the set of integers with as index (and value)
 * that parameter.
 */
static __isl_give isl_map *access_detect_parameter(__isl_take isl_map *access,
	__isl_take isl_space *space)
{
	isl_id *array_id = NULL;
	int pos = -1;

	if (isl_map_has_tuple_id(access, isl_dim_out)) {
		array_id = isl_map_get_tuple_id(access, isl_dim_out);
		pos = isl_space_find_dim_by_id(space, isl_dim_param, array_id);
	}
	isl_space_free(space);

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

/* If "expr" accesses a (0D) array that corresponds to one of the parameters
 * in "space" then replace it by a value equal to the corresponding parameter.
 */
static struct pet_expr *detect_parameter_accesses(struct pet_expr *expr,
	void *user)
{
	isl_space *space = user;

	expr->acc.access = access_detect_parameter(expr->acc.access,
						isl_space_copy(space));
	expr->acc.index = index_detect_parameter(expr->acc.index,
						isl_space_copy(space));
	if (!expr->acc.access || !expr->acc.index)
		return pet_expr_free(expr);

	return expr;
}

/* Replace all accesses to (0D) arrays that correspond to one of the parameters
 * in "space" by a value equal to the corresponding parameter.
 */
struct pet_expr *pet_expr_detect_parameter_accesses(struct pet_expr *expr,
	__isl_take isl_space *space)
{
	expr = pet_expr_map_access(expr, &detect_parameter_accesses, space);
	isl_space_free(space);
	return expr;
}

/* Add a reference identifier to access expression "expr".
 * "user" points to an integer that contains the sequence number
 * of the next reference.
 */
static struct pet_expr *access_add_ref_id(struct pet_expr *expr, void *user)
{
	isl_ctx *ctx;
	char name[50];
	int *n_ref = user;

	if (!expr)
		return expr;

	ctx = isl_map_get_ctx(expr->acc.access);
	snprintf(name, sizeof(name), "__pet_ref_%d", (*n_ref)++);
	expr->acc.ref_id = isl_id_alloc(ctx, name, NULL);
	if (!expr->acc.ref_id)
		return pet_expr_free(expr);

	return expr;
}

struct pet_expr *pet_expr_add_ref_ids(struct pet_expr *expr, int *n_ref)
{
	return pet_expr_map_access(expr, &access_add_ref_id, n_ref);
}

/* Reset the user pointer on all parameter and tuple ids in
 * the access relation and the index expressions
 * of the access expression "expr".
 */
static struct pet_expr *access_anonymize(struct pet_expr *expr, void *user)
{
	expr->acc.access = isl_map_reset_user(expr->acc.access);
	expr->acc.index = isl_multi_pw_aff_reset_user(expr->acc.index);
	if (!expr->acc.access || !expr->acc.index)
		return pet_expr_free(expr);

	return expr;
}

struct pet_expr *pet_expr_anonymize(struct pet_expr *expr)
{
	return pet_expr_map_access(expr, &access_anonymize, NULL);
}

/* Data used in access_gist() callback.
 */
struct pet_access_gist_data {
	isl_set *domain;
	isl_union_map *value_bounds;
};

/* Given an expression "expr" of type pet_expr_access, compute
 * the gist of the associated access relation and index expression
 * with respect to data->domain and the bounds on the values of the arguments
 * of the expression.
 */
static struct pet_expr *access_gist(struct pet_expr *expr, void *user)
{
	struct pet_access_gist_data *data = user;
	isl_set *domain;

	domain = isl_set_copy(data->domain);
	if (expr->n_arg > 0)
		domain = pet_value_bounds_apply(domain, expr->n_arg, expr->args,
						data->value_bounds);

	expr->acc.access = isl_map_gist_domain(expr->acc.access,
						isl_set_copy(domain));
	expr->acc.index = isl_multi_pw_aff_gist(expr->acc.index, domain);
	if (!expr->acc.access || !expr->acc.index)
		return pet_expr_free(expr);

	return expr;
}

struct pet_expr *pet_expr_gist(struct pet_expr *expr,
	__isl_keep isl_set *context, __isl_keep isl_union_map *value_bounds)
{
	struct pet_access_gist_data data = { context, value_bounds };

	return pet_expr_map_access(expr, &access_gist, &data);
}

/* Tag the access relation "access" with "id".
 * That is, insert the id as the range of a wrapped relation
 * in the domain of "access".
 *
 * If "access" is of the form
 *
 *	D[i] -> A[a]
 *
 * then the result is of the form
 *
 *	[D[i] -> id[]] -> A[a]
 */
__isl_give isl_map *pet_expr_tag_access(struct pet_expr *expr,
	__isl_take isl_map *access)
{
	isl_space *space;
	isl_map *add_tag;
	isl_id *id;

	id = isl_id_copy(expr->acc.ref_id);
	space = isl_space_range(isl_map_get_space(access));
	space = isl_space_from_range(space);
	space = isl_space_set_tuple_id(space, isl_dim_in, id);
	add_tag = isl_map_universe(space);
	access = isl_map_domain_product(access, add_tag);

	return access;
}

/* Return the relation mapping domain iterations to all possibly
 * accessed data elements.
 * In particular, take the access relation and project out the values
 * of the arguments, if any.
 */
__isl_give isl_map *pet_expr_access_get_may_access(struct pet_expr *expr)
{
	isl_map *access;
	isl_space *space;
	isl_map *map;

	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		return NULL;

	access = isl_map_copy(expr->acc.access);
	if (expr->n_arg == 0)
		return access;

	space = isl_space_domain(isl_map_get_space(access));
	map = isl_map_universe(isl_space_unwrap(space));
	map = isl_map_domain_map(map);
	access = isl_map_apply_domain(access, map);

	return access;
}

/* Return the relation mapping domain iterations to all possibly
 * accessed data elements, with its domain tagged with the reference
 * identifier.
 */
__isl_give isl_map *pet_expr_access_get_tagged_may_access(
	struct pet_expr *expr)
{
	isl_map *access;

	if (!expr)
		return NULL;

	access = pet_expr_access_get_may_access(expr);
	access = pet_expr_tag_access(expr, access);

	return access;
}

void pet_expr_dump_with_indent(struct pet_expr *expr, int indent)
{
	int i;

	if (!expr)
		return;

	fprintf(stderr, "%*s", indent, "");

	switch (expr->type) {
	case pet_expr_double:
		fprintf(stderr, "%s\n", expr->d.s);
		break;
	case pet_expr_int:
		isl_val_dump(expr->i);
		break;
	case pet_expr_access:
		if (expr->acc.ref_id) {
			isl_id_dump(expr->acc.ref_id);
			fprintf(stderr, "%*s", indent, "");
		}
		isl_map_dump(expr->acc.access);
		fprintf(stderr, "%*s", indent, "");
		isl_multi_pw_aff_dump(expr->acc.index);
		fprintf(stderr, "%*sread: %d\n", indent + 2,
				"", expr->acc.read);
		fprintf(stderr, "%*swrite: %d\n", indent + 2,
				"", expr->acc.write);
		for (i = 0; i < expr->n_arg; ++i)
			pet_expr_dump_with_indent(expr->args[i], indent + 2);
		break;
	case pet_expr_op:
		fprintf(stderr, "%s\n", op_str[expr->op]);
		for (i = 0; i < expr->n_arg; ++i)
			pet_expr_dump_with_indent(expr->args[i], indent + 2);
		break;
	case pet_expr_call:
		fprintf(stderr, "%s/%d\n", expr->name, expr->n_arg);
		for (i = 0; i < expr->n_arg; ++i)
			pet_expr_dump_with_indent(expr->args[i], indent + 2);
		break;
	case pet_expr_cast:
		fprintf(stderr, "(%s)\n", expr->type_name);
		for (i = 0; i < expr->n_arg; ++i)
			pet_expr_dump_with_indent(expr->args[i], indent + 2);
		break;
	}
}

void pet_expr_dump(struct pet_expr *expr)
{
	pet_expr_dump_with_indent(expr, 0);
}
