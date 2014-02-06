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

/* Construct a pet_expr of the given type.
 */
__isl_give pet_expr *pet_expr_alloc(isl_ctx *ctx, enum pet_expr_type type)
{
	pet_expr *expr;

	expr = isl_calloc_type(ctx, struct pet_expr);
	if (!expr)
		return NULL;

	expr->ctx = ctx;
	isl_ctx_ref(ctx);
	expr->type = type;
	expr->ref = 1;

	return expr;
}

/* Construct an access pet_expr from an access relation and an index expression.
 * By default, it is considered to be a read access.
 */
__isl_give pet_expr *pet_expr_from_access_and_index( __isl_take isl_map *access,
	__isl_take isl_multi_pw_aff *index)
{
	isl_ctx *ctx = isl_map_get_ctx(access);
	pet_expr *expr;

	if (!index || !access)
		goto error;
	expr = pet_expr_alloc(ctx, pet_expr_access);
	if (!expr)
		goto error;

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
__isl_give pet_expr *pet_expr_from_index(__isl_take isl_multi_pw_aff *index)
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

/* Construct an access pet_expr from the number of bits needed to
 * represent the type of the expression (may be zero if unknown or
 * if the type is not an integer) an index expression and
 * the depth of the accessed array.
 * By default, the access is considered to be a read access.
 *
 * If the number of indices is smaller than the depth of the array,
 * then we assume that all elements of the remaining dimensions
 * are accessed.
 */
__isl_give pet_expr *pet_expr_from_index_and_depth(int type_size,
	__isl_take isl_multi_pw_aff *index, int depth)
{
	isl_map *access;
	int dim;
	pet_expr *expr;

	access = isl_map_from_multi_pw_aff(isl_multi_pw_aff_copy(index));
	if (!access)
		goto error;
	dim = isl_map_dim(access, isl_dim_out);
	if (dim > depth)
		isl_die(isl_map_get_ctx(access), isl_error_internal,
			"number of indices greater than depth",
			access = isl_map_free(access));

	if (dim != depth)
		access = extend_range(access, depth - dim);

	expr = pet_expr_from_access_and_index(access, index);
	if (!expr)
		return NULL;

	expr->type_size = type_size;

	return expr;
error:
	isl_multi_pw_aff_free(index);
	return NULL;
}

/* Construct a pet_expr that kills the elements specified by
 * the index expression "index" and the access relation "access".
 */
__isl_give pet_expr *pet_expr_kill_from_access_and_index(
	__isl_take isl_map *access, __isl_take isl_multi_pw_aff *index)
{
	pet_expr *expr;

	if (!access || !index)
		goto error;

	expr = pet_expr_from_access_and_index(access, index);
	expr = pet_expr_access_set_read(expr, 0);
	return pet_expr_new_unary(pet_op_kill, expr);
error:
	isl_map_free(access);
	isl_multi_pw_aff_free(index);
	return NULL;
}

/* Construct a unary pet_expr that performs "op" on "arg".
 */
__isl_give pet_expr *pet_expr_new_unary(enum pet_op_type op,
	__isl_take pet_expr *arg)
{
	isl_ctx *ctx;
	pet_expr *expr;

	if (!arg)
		return NULL;
	ctx = pet_expr_get_ctx(arg);
	expr = pet_expr_alloc(ctx, pet_expr_op);
	expr = pet_expr_set_n_arg(expr, 1);
	if (!expr)
		goto error;

	expr->op = op;
	expr->args[pet_un_arg] = arg;

	return expr;
error:
	pet_expr_free(arg);
	return NULL;
}

/* Construct a binary pet_expr that performs "op" on "lhs" and "rhs",
 * where the result is represented using a type of "type_size" bits
 * (may be zero if unknown or if the type is not an integer).
 */
__isl_give pet_expr *pet_expr_new_binary(int type_size, enum pet_op_type op,
	__isl_take pet_expr *lhs, __isl_take pet_expr *rhs)
{
	isl_ctx *ctx;
	pet_expr *expr;

	if (!lhs || !rhs)
		goto error;
	ctx = pet_expr_get_ctx(lhs);
	expr = pet_expr_alloc(ctx, pet_expr_op);
	expr = pet_expr_set_n_arg(expr, 2);
	if (!expr)
		goto error;

	expr->op = op;
	expr->type_size = type_size;
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
__isl_give pet_expr *pet_expr_new_ternary(__isl_take pet_expr *cond,
	__isl_take pet_expr *lhs, __isl_take pet_expr *rhs)
{
	isl_ctx *ctx;
	pet_expr *expr;

	if (!cond || !lhs || !rhs)
		goto error;
	ctx = pet_expr_get_ctx(cond);
	expr = pet_expr_alloc(ctx, pet_expr_op);
	expr = pet_expr_set_n_arg(expr, 3);
	if (!expr)
		goto error;

	expr->op = pet_op_cond;
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
__isl_give pet_expr *pet_expr_new_call(isl_ctx *ctx, const char *name,
	unsigned n_arg)
{
	pet_expr *expr;

	expr = pet_expr_alloc(ctx, pet_expr_call);
	expr = pet_expr_set_n_arg(expr, n_arg);
	if (!expr)
		return NULL;

	expr->name = strdup(name);
	if (!expr->name)
		return pet_expr_free(expr);

	return expr;
}

/* Construct a pet_expr that represents the cast of "arg" to "type_name".
 */
__isl_give pet_expr *pet_expr_new_cast(const char *type_name,
	__isl_take pet_expr *arg)
{
	isl_ctx *ctx;
	pet_expr *expr;

	if (!arg)
		return NULL;

	ctx = pet_expr_get_ctx(arg);
	expr = pet_expr_alloc(ctx, pet_expr_cast);
	expr = pet_expr_set_n_arg(expr, 1);
	if (!expr)
		goto error;

	expr->type_name = strdup(type_name);
	if (!expr->type_name)
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
__isl_give pet_expr *pet_expr_new_double(isl_ctx *ctx,
	double val, const char *s)
{
	pet_expr *expr;

	expr = pet_expr_alloc(ctx, pet_expr_double);
	if (!expr)
		return NULL;

	expr->d.val = val;
	expr->d.s = strdup(s);
	if (!expr->d.s)
		return pet_expr_free(expr);

	return expr;
}

/* Construct a pet_expr that represents the integer value "v".
 */
__isl_give pet_expr *pet_expr_new_int(__isl_take isl_val *v)
{
	isl_ctx *ctx;
	pet_expr *expr;

	if (!v)
		return NULL;

	ctx = isl_val_get_ctx(v);
	expr = pet_expr_alloc(ctx, pet_expr_int);
	if (!expr)
		goto error;

	expr->i = v;

	return expr;
error:
	isl_val_free(v);
	return NULL;
}

static __isl_give pet_expr *pet_expr_dup(__isl_keep pet_expr *expr)
{
	int i;
	pet_expr *dup;

	if (!expr)
		return NULL;

	dup = pet_expr_alloc(expr->ctx, expr->type);
	dup = pet_expr_set_type_size(dup, expr->type_size);
	dup = pet_expr_set_n_arg(dup, expr->n_arg);
	for (i = 0; i < expr->n_arg; ++i)
		dup = pet_expr_set_arg(dup, i, pet_expr_copy(expr->args[i]));

	switch (expr->type) {
	case pet_expr_access:
		if (expr->acc.ref_id)
			dup = pet_expr_access_set_ref_id(dup,
						isl_id_copy(expr->acc.ref_id));
		dup = pet_expr_access_set_access(dup,
						isl_map_copy(expr->acc.access));
		dup = pet_expr_access_set_index(dup,
					isl_multi_pw_aff_copy(expr->acc.index));
		dup = pet_expr_access_set_read(dup, expr->acc.read);
		dup = pet_expr_access_set_write(dup, expr->acc.write);
		break;
	case pet_expr_call:
		dup = pet_expr_call_set_name(dup, expr->name);
		break;
	case pet_expr_cast:
		dup = pet_expr_cast_set_type_name(dup, expr->type_name);
		break;
	case pet_expr_double:
		dup = pet_expr_double_set(dup, expr->d.val, expr->d.s);
		break;
	case pet_expr_int:
		dup = pet_expr_int_set_val(dup, isl_val_copy(expr->i));
		break;
	case pet_expr_op:
		dup = pet_expr_op_set_type(dup, expr->op);
		break;
	case pet_expr_error:
		dup = pet_expr_free(dup);
		break;
	}

	return dup;
}

__isl_give pet_expr *pet_expr_cow(__isl_take pet_expr *expr)
{
	if (!expr)
		return NULL;

	if (expr->ref == 1)
		return expr;
	expr->ref--;
	return pet_expr_dup(expr);
}

__isl_null pet_expr *pet_expr_free(__isl_take pet_expr *expr)
{
	int i;

	if (!expr)
		return NULL;
	if (--expr->ref > 0)
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
	case pet_expr_error:
		break;
	}

	isl_ctx_deref(expr->ctx);
	free(expr);
	return NULL;
}

/* Return an additional reference to "expr".
 */
__isl_give pet_expr *pet_expr_copy(__isl_keep pet_expr *expr)
{
	if (!expr)
		return NULL;

	expr->ref++;
	return expr;
}

/* Return the isl_ctx in which "expr" was created.
 */
isl_ctx *pet_expr_get_ctx(__isl_keep pet_expr *expr)
{
	return expr ? expr->ctx : NULL;
}

/* Return the type of "expr".
 */
enum pet_expr_type pet_expr_get_type(__isl_keep pet_expr *expr)
{
	if (!expr)
		return pet_expr_error;
	return expr->type;
}

/* Return the number of arguments of "expr".
 */
int pet_expr_get_n_arg(__isl_keep pet_expr *expr)
{
	if (!expr)
		return -1;

	return expr->n_arg;
}

/* Set the number of arguments of "expr" to "n".
 *
 * If "expr" originally had more arguments, then remove the extra arguments.
 * If "expr" originally had fewer arguments, then create space for
 * the extra arguments ans initialize them to NULL.
 */
__isl_give pet_expr *pet_expr_set_n_arg(__isl_take pet_expr *expr, int n)
{
	int i;
	pet_expr **args;

	if (!expr)
		return NULL;
	if (expr->n_arg == n)
		return expr;
	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;

	if (n < expr->n_arg) {
		for (i = n; i < expr->n_arg; ++i)
			pet_expr_free(expr->args[i]);
		expr->n_arg = n;
		return expr;
	}

	args = isl_realloc_array(expr->ctx, expr->args, pet_expr *, n);
	if (!args)
		return pet_expr_free(expr);
	expr->args = args;
	for (i = expr->n_arg; i < n; ++i)
		expr->args[i] = NULL;
	expr->n_arg = n;

	return expr;
}

/* Return the argument of "expr" at position "pos".
 */
__isl_give pet_expr *pet_expr_get_arg(__isl_keep pet_expr *expr, int pos)
{
	if (!expr)
		return NULL;
	if (pos < 0 || pos >= expr->n_arg)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"position out of bounds", return NULL);

	return pet_expr_copy(expr->args[pos]);
}

/* Replace the argument of "expr" at position "pos" by "arg".
 */
__isl_give pet_expr *pet_expr_set_arg(__isl_take pet_expr *expr, int pos,
	__isl_take pet_expr *arg)
{
	if (!expr || !arg)
		goto error;
	if (pos < 0 || pos >= expr->n_arg)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"position out of bounds", goto error);
	if (expr->args[pos] == arg) {
		pet_expr_free(arg);
		return expr;
	}

	expr = pet_expr_cow(expr);
	if (!expr)
		goto error;

	pet_expr_free(expr->args[pos]);
	expr->args[pos] = arg;

	return expr;
error:
	pet_expr_free(expr);
	pet_expr_free(arg);
	return NULL;
}

/* Does "expr" perform a comparison operation?
 */
int pet_expr_is_comparison(__isl_keep pet_expr *expr)
{
	if (!expr)
		return -1;
	if (expr->type != pet_expr_op)
		return 0;
	switch (expr->op) {
	case pet_op_eq:
	case pet_op_ne:
	case pet_op_le:
	case pet_op_ge:
	case pet_op_lt:
	case pet_op_gt:
		return 1;
	default:
		return 0;
	}
}

/* Does "expr" perform a boolean operation?
 */
int pet_expr_is_boolean(__isl_keep pet_expr *expr)
{
	if (!expr)
		return -1;
	if (expr->type != pet_expr_op)
		return 0;
	switch (expr->op) {
	case pet_op_land:
	case pet_op_lor:
	case pet_op_lnot:
		return 1;
	default:
		return 0;
	}
}

/* Does "expr" perform a min operation?
 */
int pet_expr_is_min(__isl_keep pet_expr *expr)
{
	if (!expr)
		return -1;
	if (expr->type != pet_expr_call)
		return 0;
	if (expr->n_arg != 2)
		return 0;
	if (strcmp(expr->name, "min") != 0)
		return 0;
	return 1;
}

/* Does "expr" perform a max operation?
 */
int pet_expr_is_max(__isl_keep pet_expr *expr)
{
	if (!expr)
		return -1;
	if (expr->type != pet_expr_call)
		return 0;
	if (expr->n_arg != 2)
		return 0;
	if (strcmp(expr->name, "max") != 0)
		return 0;
	return 1;
}

/* Does "expr" represent an access to an unnamed space, i.e.,
 * does it represent an affine expression?
 */
int pet_expr_is_affine(__isl_keep pet_expr *expr)
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

/* Does "expr" represent an access to a scalar, i.e., a zero-dimensional array,
 * not part of any struct?
 */
int pet_expr_is_scalar_access(__isl_keep pet_expr *expr)
{
	if (!expr)
		return -1;
	if (expr->type != pet_expr_access)
		return 0;
	if (isl_map_range_is_wrapping(expr->acc.access))
		return 0;

	return isl_map_dim(expr->acc.access, isl_dim_out) == 0;
}

/* Return 1 if the two pet_exprs are equivalent.
 */
int pet_expr_is_equal(__isl_keep pet_expr *expr1, __isl_keep pet_expr *expr2)
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
	case pet_expr_error:
		return -1;
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

/* Does the access expression "expr" read the accessed elements?
 */
int pet_expr_access_is_read(__isl_keep pet_expr *expr)
{
	if (!expr)
		return -1;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return -1);

	return expr->acc.read;
}

/* Does the access expression "expr" write to the accessed elements?
 */
int pet_expr_access_is_write(__isl_keep pet_expr *expr)
{
	if (!expr)
		return -1;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return -1);

	return expr->acc.write;
}

/* Return the identifier of the array accessed by "expr".
 *
 * If "expr" represents a member access, then return the identifier
 * of the outer structure array.
 */
__isl_give isl_id *pet_expr_access_get_id(__isl_keep pet_expr *expr)
{
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return NULL);

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
__isl_give isl_space *pet_expr_access_get_parameter_space(
	__isl_keep pet_expr *expr)
{
	isl_space *space;

	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return NULL);

	space = isl_multi_pw_aff_get_space(expr->acc.index);
	space = isl_space_params(space);

	return space;
}

/* Return the space of the data accessed by "expr".
 */
__isl_give isl_space *pet_expr_access_get_data_space(__isl_keep pet_expr *expr)
{
	isl_space *space;

	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return NULL);

	space = isl_multi_pw_aff_get_space(expr->acc.index);
	space = isl_space_range(space);

	return space;
}

/* Modify all expressions of type pet_expr_access in "expr"
 * by calling "fn" on them.
 */
__isl_give pet_expr *pet_expr_map_access(__isl_take pet_expr *expr,
	__isl_give pet_expr *(*fn)(__isl_take pet_expr *expr, void *user),
	void *user)
{
	int i, n;

	n = pet_expr_get_n_arg(expr);
	for (i = 0; i < n; ++i) {
		pet_expr *arg = pet_expr_get_arg(expr, i);
		arg = pet_expr_map_access(arg, fn, user);
		expr = pet_expr_set_arg(expr, i, arg);
	}

	if (!expr)
		return NULL;

	if (expr->type == pet_expr_access)
		expr = fn(expr, user);

	return expr;
}

/* Call "fn" on each of the subexpressions of "expr" of type "type".
 *
 * Return -1 on error (where fn returning a negative value is treated as
 * an error).
 * Otherwise return 0.
 */
int pet_expr_foreach_expr_of_type(__isl_keep pet_expr *expr,
	enum pet_expr_type type,
	int (*fn)(__isl_keep pet_expr *expr, void *user), void *user)
{
	int i;

	if (!expr)
		return -1;

	for (i = 0; i < expr->n_arg; ++i)
		if (pet_expr_foreach_expr_of_type(expr->args[i],
						    type, fn, user) < 0)
			return -1;

	if (expr->type == type)
		return fn(expr, user);

	return 0;
}

/* Call "fn" on each of the subexpressions of "expr" of type pet_expr_access.
 *
 * Return -1 on error (where fn returning a negative value is treated as
 * an error).
 * Otherwise return 0.
 */
int pet_expr_foreach_access_expr(__isl_keep pet_expr *expr,
	int (*fn)(__isl_keep pet_expr *expr, void *user), void *user)
{
	return pet_expr_foreach_expr_of_type(expr, pet_expr_access, fn, user);
}

/* Call "fn" on each of the subexpressions of "expr" of type pet_expr_call.
 *
 * Return -1 on error (where fn returning a negative value is treated as
 * an error).
 * Otherwise return 0.
 */
int pet_expr_foreach_call_expr(__isl_keep pet_expr *expr,
	int (*fn)(__isl_keep pet_expr *expr, void *user), void *user)
{
	return pet_expr_foreach_expr_of_type(expr, pet_expr_call, fn, user);
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
static int writes(__isl_keep pet_expr *expr, void *user)
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
int pet_expr_writes(__isl_keep pet_expr *expr, __isl_keep isl_id *id)
{
	struct pet_expr_writes_data data;

	data.id = id;
	data.found = 0;
	if (pet_expr_foreach_access_expr(expr, &writes, &data) < 0 &&
	    !data.found)
		return -1;

	return data.found;
}

/* Move the "n" dimensions of "src_type" starting at "src_pos" of
 * index expression and access relation of "expr"
 * to dimensions of "dst_type" at "dst_pos".
 */
__isl_give pet_expr *pet_expr_access_move_dims(__isl_take pet_expr *expr,
	enum isl_dim_type dst_type, unsigned dst_pos,
	enum isl_dim_type src_type, unsigned src_pos, unsigned n)
{
	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access pet_expr", return pet_expr_free(expr));

	expr->acc.access = isl_map_move_dims(expr->acc.access,
				dst_type, dst_pos, src_type, src_pos, n);
	expr->acc.index = isl_multi_pw_aff_move_dims(expr->acc.index,
				dst_type, dst_pos, src_type, src_pos, n);
	if (!expr->acc.access || !expr->acc.index)
		return pet_expr_free(expr);

	return expr;
}

/* Replace the index expression and access relation of "expr"
 * by their preimages under the function represented by "ma".
 */
__isl_give pet_expr *pet_expr_access_pullback_multi_aff(
	__isl_take pet_expr *expr, __isl_take isl_multi_aff *ma)
{
	expr = pet_expr_cow(expr);
	if (!expr || !ma)
		goto error;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access pet_expr", goto error);

	expr->acc.access = isl_map_preimage_domain_multi_aff(expr->acc.access,
						isl_multi_aff_copy(ma));
	expr->acc.index = isl_multi_pw_aff_pullback_multi_aff(expr->acc.index,
						ma);
	if (!expr->acc.access || !expr->acc.index)
		return pet_expr_free(expr);

	return expr;
error:
	isl_multi_aff_free(ma);
	pet_expr_free(expr);
	return NULL;
}

/* Return the access relation of access expression "expr".
 */
__isl_give isl_map *pet_expr_access_get_access(__isl_keep pet_expr *expr)
{
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return NULL);

	return isl_map_copy(expr->acc.access);
}

/* Return the index expression of access expression "expr".
 */
__isl_give isl_multi_pw_aff *pet_expr_access_get_index(
	__isl_keep pet_expr *expr)
{
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return NULL);

	return isl_multi_pw_aff_copy(expr->acc.index);
}

/* Align the parameters of expr->acc.index and expr->acc.access.
 */
__isl_give pet_expr *pet_expr_access_align_params(__isl_take pet_expr *expr)
{
	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return pet_expr_free(expr));

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
__isl_give pet_expr *pet_expr_restrict(__isl_take pet_expr *expr,
	__isl_take isl_set *cond)
{
	int i;

	expr = pet_expr_cow(expr);
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
__isl_give pet_expr *pet_expr_access_update_domain(__isl_take pet_expr *expr,
	__isl_keep isl_multi_pw_aff *update)
{
	isl_space *space;

	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return pet_expr_free(expr));

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

static __isl_give pet_expr *update_domain(__isl_take pet_expr *expr, void *user)
{
	isl_multi_pw_aff *update = user;

	return pet_expr_access_update_domain(expr, update);
}

/* Modify all access relations in "expr" by precomposing them with
 * the given iteration space transformation.
 */
__isl_give pet_expr *pet_expr_update_domain(__isl_take pet_expr *expr,
	__isl_take isl_multi_pw_aff *update)
{
	expr = pet_expr_map_access(expr, &update_domain, update);
	isl_multi_pw_aff_free(update);
	return expr;
}

/* Add all parameters in "space" to the access relation and index expression
 * of "expr".
 */
static __isl_give pet_expr *align_params(__isl_take pet_expr *expr, void *user)
{
	isl_space *space = user;

	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return pet_expr_free(expr));

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
__isl_give pet_expr *pet_expr_align_params(__isl_take pet_expr *expr,
	__isl_take isl_space *space)
{
	expr = pet_expr_map_access(expr, &align_params, space);
	isl_space_free(space);
	return expr;
}

/* Insert an argument expression corresponding to "test" in front
 * of the list of arguments described by *n_arg and *args.
 */
static __isl_give pet_expr *insert_access_arg(__isl_take pet_expr *expr,
	__isl_keep isl_multi_pw_aff *test)
{
	int i;
	isl_ctx *ctx = isl_multi_pw_aff_get_ctx(test);

	if (!test)
		return pet_expr_free(expr);
	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;

	if (!expr->args) {
		expr->args = isl_calloc_array(ctx, pet_expr *, 1);
		if (!expr->args)
			return pet_expr_free(expr);
	} else {
		pet_expr **ext;
		ext = isl_calloc_array(ctx, pet_expr *, 1 + expr->n_arg);
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
__isl_give pet_expr *pet_expr_filter(__isl_take pet_expr *expr,
	__isl_take isl_multi_pw_aff *test, int satisfied)
{
	isl_id *id;
	isl_ctx *ctx;
	isl_space *space;
	isl_pw_multi_aff *pma;

	expr = pet_expr_cow(expr);
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
static __isl_give pet_expr *detect_parameter_accesses(__isl_take pet_expr *expr,
	void *user)
{
	isl_space *space = user;

	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return pet_expr_free(expr));

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
__isl_give pet_expr *pet_expr_detect_parameter_accesses(
	__isl_take pet_expr *expr, __isl_take isl_space *space)
{
	expr = pet_expr_map_access(expr, &detect_parameter_accesses, space);
	isl_space_free(space);
	return expr;
}

/* Add a reference identifier to access expression "expr".
 * "user" points to an integer that contains the sequence number
 * of the next reference.
 */
static __isl_give pet_expr *access_add_ref_id(__isl_take pet_expr *expr,
	void *user)
{
	isl_ctx *ctx;
	char name[50];
	int *n_ref = user;

	expr = pet_expr_cow(expr);
	if (!expr)
		return expr;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return pet_expr_free(expr));

	ctx = isl_map_get_ctx(expr->acc.access);
	snprintf(name, sizeof(name), "__pet_ref_%d", (*n_ref)++);
	expr->acc.ref_id = isl_id_alloc(ctx, name, NULL);
	if (!expr->acc.ref_id)
		return pet_expr_free(expr);

	return expr;
}

__isl_give pet_expr *pet_expr_add_ref_ids(__isl_take pet_expr *expr, int *n_ref)
{
	return pet_expr_map_access(expr, &access_add_ref_id, n_ref);
}

/* Reset the user pointer on all parameter and tuple ids in
 * the access relation and the index expressions
 * of the access expression "expr".
 */
static __isl_give pet_expr *access_anonymize(__isl_take pet_expr *expr,
	void *user)
{
	expr = pet_expr_cow(expr);
	if (!expr)
		return expr;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return pet_expr_free(expr));

	expr->acc.access = isl_map_reset_user(expr->acc.access);
	expr->acc.index = isl_multi_pw_aff_reset_user(expr->acc.index);
	if (!expr->acc.access || !expr->acc.index)
		return pet_expr_free(expr);

	return expr;
}

__isl_give pet_expr *pet_expr_anonymize(__isl_take pet_expr *expr)
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
static __isl_give pet_expr *access_gist(__isl_take pet_expr *expr, void *user)
{
	struct pet_access_gist_data *data = user;
	isl_set *domain;

	expr = pet_expr_cow(expr);
	if (!expr)
		return expr;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return pet_expr_free(expr));

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

__isl_give pet_expr *pet_expr_gist(__isl_take pet_expr *expr,
	__isl_keep isl_set *context, __isl_keep isl_union_map *value_bounds)
{
	struct pet_access_gist_data data = { context, value_bounds };

	return pet_expr_map_access(expr, &access_gist, &data);
}

/* Mark "expr" as a read dependening on "read".
 */
__isl_give pet_expr *pet_expr_access_set_read(__isl_take pet_expr *expr,
	int read)
{
	if (!expr)
		return pet_expr_free(expr);
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return pet_expr_free(expr));
	if (expr->acc.read == read)
		return expr;
	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;
	expr->acc.read = read;

	return expr;
}

/* Mark "expr" as a write dependening on "write".
 */
__isl_give pet_expr *pet_expr_access_set_write(__isl_take pet_expr *expr,
	int write)
{
	if (!expr)
		return pet_expr_free(expr);
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return pet_expr_free(expr));
	if (expr->acc.write == write)
		return expr;
	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;
	expr->acc.write = write;

	return expr;
}

/* Replace the access relation of "expr" by "access".
 */
__isl_give pet_expr *pet_expr_access_set_access(__isl_take pet_expr *expr,
	__isl_take isl_map *access)
{
	expr = pet_expr_cow(expr);
	if (!expr || !access)
		goto error;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", goto error);
	isl_map_free(expr->acc.access);
	expr->acc.access = access;

	return expr;
error:
	isl_map_free(access);
	pet_expr_free(expr);
	return NULL;
}

/* Replace the index expression of "expr" by "index".
 */
__isl_give pet_expr *pet_expr_access_set_index(__isl_take pet_expr *expr,
	__isl_take isl_multi_pw_aff *index)
{
	expr = pet_expr_cow(expr);
	if (!expr || !index)
		goto error;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", goto error);
	isl_multi_pw_aff_free(expr->acc.index);
	expr->acc.index = index;

	return expr;
error:
	isl_multi_pw_aff_free(index);
	pet_expr_free(expr);
	return NULL;
}

/* Return the reference identifier of access expression "expr".
 */
__isl_give isl_id *pet_expr_access_get_ref_id(__isl_keep pet_expr *expr)
{
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return NULL);

	return isl_id_copy(expr->acc.ref_id);
}

/* Replace the reference identifier of access expression "expr" by "ref_id".
 */
__isl_give pet_expr *pet_expr_access_set_ref_id(__isl_take pet_expr *expr,
	__isl_take isl_id *ref_id)
{
	expr = pet_expr_cow(expr);
	if (!expr || !ref_id)
		goto error;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", goto error);
	isl_id_free(expr->acc.ref_id);
	expr->acc.ref_id = ref_id;

	return expr;
error:
	isl_id_free(ref_id);
	pet_expr_free(expr);
	return NULL;
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
__isl_give isl_map *pet_expr_tag_access(__isl_keep pet_expr *expr,
	__isl_take isl_map *access)
{
	isl_space *space;
	isl_map *add_tag;
	isl_id *id;

	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression",
			return isl_map_free(access));

	id = isl_id_copy(expr->acc.ref_id);
	space = isl_space_range(isl_map_get_space(access));
	space = isl_space_from_range(space);
	space = isl_space_set_tuple_id(space, isl_dim_in, id);
	add_tag = isl_map_universe(space);
	access = isl_map_domain_product(access, add_tag);

	return access;
}

/* Return the relation mapping pairs of domain iterations and argument
 * values to the corresponding accessed data elements.
 */
__isl_give isl_map *pet_expr_access_get_dependent_access(
	__isl_keep pet_expr *expr)
{
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return NULL);

	return isl_map_copy(expr->acc.access);
}

/* Return the relation mapping domain iterations to all possibly
 * accessed data elements.
 * In particular, take the access relation and project out the values
 * of the arguments, if any.
 */
__isl_give isl_map *pet_expr_access_get_may_access(__isl_keep pet_expr *expr)
{
	isl_map *access;
	isl_space *space;
	isl_map *map;

	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return NULL);

	access = pet_expr_access_get_dependent_access(expr);
	if (expr->n_arg == 0)
		return access;

	space = isl_space_domain(isl_map_get_space(access));
	map = isl_map_universe(isl_space_unwrap(space));
	map = isl_map_domain_map(map);
	access = isl_map_apply_domain(access, map);

	return access;
}

/* Return a relation mapping domain iterations to definitely
 * accessed data elements, assuming the statement containing
 * the expression is executed.
 *
 * If there are no arguments, then all elements are accessed.
 * Otherwise, we conservatively return an empty relation.
 */
__isl_give isl_map *pet_expr_access_get_must_access(__isl_keep pet_expr *expr)
{
	isl_space *space;

	if (!expr)
		return NULL;
	if (expr->type != pet_expr_access)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an access expression", return NULL);

	if (expr->n_arg == 0)
		return pet_expr_access_get_dependent_access(expr);

	space = isl_map_get_space(expr->acc.access);
	space = isl_space_domain_factor_domain(space);

	return isl_map_empty(space);
}

/* Return the relation mapping domain iterations to all possibly
 * accessed data elements, with its domain tagged with the reference
 * identifier.
 */
__isl_give isl_map *pet_expr_access_get_tagged_may_access(
	__isl_keep pet_expr *expr)
{
	isl_map *access;

	if (!expr)
		return NULL;

	access = pet_expr_access_get_may_access(expr);
	access = pet_expr_tag_access(expr, access);

	return access;
}

/* Return the operation type of operation expression "expr".
 */
enum pet_op_type pet_expr_op_get_type(__isl_keep pet_expr *expr)
{
	if (!expr)
		return pet_op_last;
	if (expr->type != pet_expr_op)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an operation expression", return pet_op_last);

	return expr->op;
}

/* Replace the operation type of operation expression "expr" by "type".
 */
__isl_give pet_expr *pet_expr_op_set_type(__isl_take pet_expr *expr,
	enum pet_op_type type)
{
	if (!expr)
		return pet_expr_free(expr);
	if (expr->type != pet_expr_op)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an operation expression",
			return pet_expr_free(expr));
	if (expr->op == type)
		return expr;
	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;
	expr->op = type;

	return expr;
}

/* Return the name of the function called by "expr".
 */
__isl_keep const char *pet_expr_call_get_name(__isl_keep pet_expr *expr)
{
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_call)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not a call expression", return NULL);
	return expr->name;
}

/* Replace the name of the function called by "expr" by "name".
 */
__isl_give pet_expr *pet_expr_call_set_name(__isl_take pet_expr *expr,
	__isl_keep const char *name)
{
	expr = pet_expr_cow(expr);
	if (!expr || !name)
		return pet_expr_free(expr);
	if (expr->type != pet_expr_call)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not a call expression", return pet_expr_free(expr));
	free(expr->name);
	expr->name = strdup(name);
	if (!expr->name)
		return pet_expr_free(expr);
	return expr;
}

/* Replace the type of the cast performed by "expr" by "name".
 */
__isl_give pet_expr *pet_expr_cast_set_type_name(__isl_take pet_expr *expr,
	__isl_keep const char *name)
{
	expr = pet_expr_cow(expr);
	if (!expr || !name)
		return pet_expr_free(expr);
	if (expr->type != pet_expr_cast)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not a cast expression", return pet_expr_free(expr));
	free(expr->type_name);
	expr->type_name = strdup(name);
	if (!expr->type_name)
		return pet_expr_free(expr);
	return expr;
}

/* Return the value of the integer represented by "expr".
 */
__isl_give isl_val *pet_expr_int_get_val(__isl_keep pet_expr *expr)
{
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_int)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an int expression", return NULL);

	return isl_val_copy(expr->i);
}

/* Replace the value of the integer represented by "expr" by "v".
 */
__isl_give pet_expr *pet_expr_int_set_val(__isl_take pet_expr *expr,
	__isl_take isl_val *v)
{
	expr = pet_expr_cow(expr);
	if (!expr || !v)
		goto error;
	if (expr->type != pet_expr_int)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not an int expression", goto error);
	isl_val_free(expr->i);
	expr->i = v;

	return expr;
error:
	isl_val_free(v);
	pet_expr_free(expr);
	return NULL;
}

/* Replace the value and string representation of the double
 * represented by "expr" by "d" and "s".
 */
__isl_give pet_expr *pet_expr_double_set(__isl_take pet_expr *expr,
	double d, __isl_keep const char *s)
{
	expr = pet_expr_cow(expr);
	if (!expr || !s)
		return pet_expr_free(expr);
	if (expr->type != pet_expr_double)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not a double expression", return pet_expr_free(expr));
	expr->d.val = d;
	free(expr->d.s);
	expr->d.s = strdup(s);
	if (!expr->d.s)
		return pet_expr_free(expr);
	return expr;
}

/* Return a string representation of the double expression "expr".
 */
__isl_give char *pet_expr_double_get_str(__isl_keep pet_expr *expr)
{
	if (!expr)
		return NULL;
	if (expr->type != pet_expr_double)
		isl_die(pet_expr_get_ctx(expr), isl_error_invalid,
			"not a double expression", return NULL);
	return strdup(expr->d.s);
}

/* Return the number of bits needed to represent the type of "expr".
 * See the description of the type_size field of pet_expr.
 */
int pet_expr_get_type_size(__isl_keep pet_expr *expr)
{
	return expr ? expr->type_size : 0;
}

/* Replace the number of bits needed to represent the type of "expr"
 * by "type_size".
 * See the description of the type_size field of pet_expr.
 */
__isl_give pet_expr *pet_expr_set_type_size(__isl_take pet_expr *expr,
	int type_size)
{
	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;

	expr->type_size = type_size;

	return expr;
}

void pet_expr_dump_with_indent(__isl_keep pet_expr *expr, int indent)
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
	case pet_expr_error:
		fprintf(stderr, "ERROR\n");
		break;
	}
}

void pet_expr_dump(__isl_keep pet_expr *expr)
{
	pet_expr_dump_with_indent(expr, 0);
}
