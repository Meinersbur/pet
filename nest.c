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
#include "expr_arg.h"
#include "nest.h"
#include "scop.h"

/* A wrapper around pet_expr_free to be used as an isl_id free user function.
 */
static void pet_expr_free_wrap(void *user)
{
	pet_expr_free((pet_expr *) user);
}

/* Create an isl_id that refers to the nested access "expr".
 */
__isl_give isl_id *pet_nested_pet_expr(__isl_take pet_expr *expr)
{
	isl_id *id;

	id = isl_id_alloc(pet_expr_get_ctx(expr), "__pet_expr", expr);
	id = isl_id_set_free_user(id, &pet_expr_free_wrap);

	return id;
}

/* Extract a pet_expr from an isl_id created by pet_nested_pet_expr.
 * Such an isl_id has name "__pet_expr" and
 * the user pointer points to a pet_expr object.
 */
__isl_give pet_expr *pet_nested_extract_expr(__isl_keep isl_id *id)
{
	return pet_expr_copy((pet_expr *) isl_id_get_user(id));
}

/* Does "id" refer to a nested access created by pet_nested_pet_expr?
 */
int pet_nested_in_id(__isl_keep isl_id *id)
{
	const char *name;

	if (!id)
		return 0;
	if (!isl_id_get_user(id))
		return 0;

	name = isl_id_get_name(id);
	return !strcmp(name, "__pet_expr");
}

/* Does parameter "pos" of "space" refer to a nested access?
 */
static int pet_nested_in_space(__isl_keep isl_space *space, int pos)
{
	int nested;
	isl_id *id;

	id = isl_space_get_dim_id(space, isl_dim_param, pos);
	nested = pet_nested_in_id(id);
	isl_id_free(id);

	return nested;
}

/* Does parameter "pos" of "set" refer to a nested access?
 */
int pet_nested_in_set(__isl_keep isl_set *set, int pos)
{
	int nested;
	isl_id *id;

	id = isl_set_get_dim_id(set, isl_dim_param, pos);
	nested = pet_nested_in_id(id);
	isl_id_free(id);

	return nested;
}

/* Does parameter "pos" of "map" refer to a nested access?
 */
int pet_nested_in_map(__isl_keep isl_map *map, int pos)
{
	int nested;
	isl_id *id;

	id = isl_map_get_dim_id(map, isl_dim_param, pos);
	nested = pet_nested_in_id(id);
	isl_id_free(id);

	return nested;
}

/* Does "space" involve any parameters that refer to nested accesses?
 */
int pet_nested_any_in_space(__isl_keep isl_space *space)
{
	int i;
	int nparam;

	nparam = isl_space_dim(space, isl_dim_param);
	for (i = 0; i < nparam; ++i)
		if (pet_nested_in_space(space, i))
			return 1;

	return 0;
}

/* Does "pa" involve any parameters that refer to nested accesses?
 */
int pet_nested_any_in_pw_aff(__isl_keep isl_pw_aff *pa)
{
	isl_space *space;
	int nested;

	space = isl_pw_aff_get_space(pa);
	nested = pet_nested_any_in_space(space);
	isl_space_free(space);

	return nested;
}

/* How many parameters of "space" refer to nested accesses?
 */
int pet_nested_n_in_space(__isl_keep isl_space *space)
{
	int i, n = 0;
	int nparam;

	nparam = isl_space_dim(space, isl_dim_param);
	for (i = 0; i < nparam; ++i)
		if (pet_nested_in_space(space, i))
			++n;

	return n;
}

/* How many parameters of "map" refer to nested accesses?
 */
int pet_nested_n_in_map(__isl_keep isl_map *map)
{
	isl_space *space;
	int n;

	space = isl_map_get_space(map);
	n = pet_nested_n_in_space(space);
	isl_space_free(space);

	return n;
}

/* How many parameters of "set" refer to nested accesses?
 */
int pet_nested_n_in_set(__isl_keep isl_set *set)
{
	isl_space *space;
	int n;

	space = isl_set_get_space(set);
	n = pet_nested_n_in_space(space);
	isl_space_free(space);

	return n;
}

/* Remove all parameters from "set" that refer to nested accesses.
 */
__isl_give isl_set *pet_nested_remove_from_set(__isl_take isl_set *set)
{
	int i;
	int nparam;

	nparam = isl_set_dim(set, isl_dim_param);
	for (i = nparam - 1; i >= 0; --i)
		if (pet_nested_in_set(set, i))
			set = isl_set_project_out(set, isl_dim_param, i, 1);

	return set;
}

/* Remove all parameters from "map" that refer to nested accesses.
 */
static __isl_give isl_map *pet_nested_remove_from_map(__isl_take isl_map *map)
{
	int i;
	int nparam;

	nparam = isl_map_dim(map, isl_dim_param);
	for (i = nparam - 1; i >= 0; --i)
		if (pet_nested_in_map(map, i))
			map = isl_map_project_out(map, isl_dim_param, i, 1);

	return map;
}

/* Remove all parameters from "mpa" that refer to nested accesses.
 */
static __isl_give isl_multi_pw_aff *pet_nested_remove_from_multi_pw_aff(
	__isl_take isl_multi_pw_aff *mpa)
{
	int i;
	int nparam;
	isl_space *space;

	space = isl_multi_pw_aff_get_space(mpa);
	nparam = isl_space_dim(space, isl_dim_param);
	for (i = nparam - 1; i >= 0; --i) {
		if (!pet_nested_in_space(space, i))
			continue;
		mpa = isl_multi_pw_aff_drop_dims(mpa, isl_dim_param, i, 1);
	}
	isl_space_free(space);

	return mpa;
}

/* Remove all parameters from the index expression and access relation of "expr"
 * that refer to nested accesses.
 */
static __isl_give pet_expr *expr_remove_nested_parameters(
	__isl_take pet_expr *expr, void *user)
{
	expr = pet_expr_cow(expr);
	if (!expr)
		return NULL;

	expr->acc.access = pet_nested_remove_from_map(expr->acc.access);
	expr->acc.index = pet_nested_remove_from_multi_pw_aff(expr->acc.index);
	if (!expr->acc.access || !expr->acc.index)
		return pet_expr_free(expr);

	return expr;
}

/* Remove all nested access parameters from the schedule and all
 * accesses of "stmt".
 * There is no need to remove them from the domain as these parameters
 * have already been removed from the domain when this function is called.
 */
struct pet_stmt *pet_stmt_remove_nested_parameters(struct pet_stmt *stmt)
{
	int i;

	if (!stmt)
		return NULL;
	stmt->schedule = pet_nested_remove_from_map(stmt->schedule);
	stmt->body = pet_expr_map_access(stmt->body,
			    &expr_remove_nested_parameters, NULL);
	if (!stmt->schedule || !stmt->body)
		goto error;
	for (i = 0; i < stmt->n_arg; ++i) {
		stmt->args[i] = pet_expr_map_access(stmt->args[i],
			    &expr_remove_nested_parameters, NULL);
		if (!stmt->args[i])
			goto error;
	}

	return stmt;
error:
	pet_stmt_free(stmt);
	return NULL;
}

/* For each nested access parameter in "space",
 * construct a corresponding pet_expr, place it in args and
 * record its position in "param2pos".
 * "n_arg" is the number of elements that are already in args.
 * The position recorded in "param2pos" takes this number into account.
 * If the pet_expr corresponding to a parameter is identical to
 * the pet_expr corresponding to an earlier parameter, then these two
 * parameters are made to refer to the same element in args.
 *
 * Return the final number of elements in args or -1 if an error has occurred.
 */
int pet_extract_nested_from_space(__isl_keep isl_space *space,
	int n_arg, __isl_give pet_expr **args, int *param2pos)
{
	int i, nparam;

	nparam = isl_space_dim(space, isl_dim_param);
	for (i = 0; i < nparam; ++i) {
		int j;
		isl_id *id = isl_space_get_dim_id(space, isl_dim_param, i);

		if (!pet_nested_in_id(id)) {
			isl_id_free(id);
			continue;
		}

		args[n_arg] = pet_nested_extract_expr(id);
		isl_id_free(id);
		if (!args[n_arg])
			return -1;

		for (j = 0; j < n_arg; ++j)
			if (pet_expr_is_equal(args[j], args[n_arg]))
				break;

		if (j < n_arg) {
			pet_expr_free(args[n_arg]);
			args[n_arg] = NULL;
			param2pos[i] = j;
		} else
			param2pos[i] = n_arg++;
	}

	return n_arg;
}

/* For each nested access parameter in the access relations in "expr",
 * construct a corresponding pet_expr, append it to the arguments of "expr"
 * and record its position in "param2pos" (relative to the initial
 * number of arguments).
 * n is the number of nested access parameters.
 */
__isl_give pet_expr *pet_expr_extract_nested(__isl_take pet_expr *expr, int n,
	int *param2pos)
{
	isl_ctx *ctx;
	isl_space *space;
	int i, n_arg;
	pet_expr **args;

	ctx = pet_expr_get_ctx(expr);
	args = isl_calloc_array(ctx, pet_expr *, n);
	if (!args)
		return pet_expr_free(expr);

	n_arg = pet_expr_get_n_arg(expr);
	space = pet_expr_access_get_parameter_space(expr);
	n = pet_extract_nested_from_space(space, 0, args, param2pos);
	isl_space_free(space);

	if (n < 0)
		expr = pet_expr_free(expr);
	else
		expr = pet_expr_set_n_arg(expr, n_arg + n);

	for (i = 0; i < n; ++i)
		expr = pet_expr_set_arg(expr, n_arg + i, args[i]);
	free(args);

	return expr;
}

/* Are "expr1" and "expr2" both array accesses such that
 * the access relation of "expr1" is a subset of that of "expr2"?
 * Only take into account the first "n_arg" arguments.
 */
static int is_sub_access(__isl_keep pet_expr *expr1, __isl_keep pet_expr *expr2,
	int n_arg)
{
	isl_id *id1, *id2;
	isl_map *access1, *access2;
	int is_subset;
	int i, n1, n2;

	if (!expr1 || !expr2)
		return 0;
	if (pet_expr_get_type(expr1) != pet_expr_access)
		return 0;
	if (pet_expr_get_type(expr2) != pet_expr_access)
		return 0;
	if (pet_expr_is_affine(expr1))
		return 0;
	if (pet_expr_is_affine(expr2))
		return 0;
	n1 = pet_expr_get_n_arg(expr1);
	if (n1 > n_arg)
		n1 = n_arg;
	n2 = pet_expr_get_n_arg(expr2);
	if (n2 > n_arg)
		n2 = n_arg;
	if (n1 != n2)
		return 0;
	for (i = 0; i < n1; ++i) {
		pet_expr *arg1, *arg2;
		int equal;
		arg1 = pet_expr_get_arg(expr1, i);
		arg2 = pet_expr_get_arg(expr2, i);
		equal = pet_expr_is_equal(arg1, arg2);
		pet_expr_free(arg1);
		pet_expr_free(arg2);
		if (equal < 0 || !equal)
			return equal;
	}
	id1 = pet_expr_access_get_id(expr1);
	id2 = pet_expr_access_get_id(expr2);
	isl_id_free(id1);
	isl_id_free(id2);
	if (!id1 || !id2)
		return 0;
	if (id1 != id2)
		return 0;

	access1 = pet_expr_access_get_access(expr1);
	access2 = pet_expr_access_get_access(expr2);
	is_subset = isl_map_is_subset(access1, access2);
	isl_map_free(access1);
	isl_map_free(access2);

	return is_subset;
}

/* Mark self dependences among the arguments of "expr" starting at "first".
 * These arguments have already been added to the list of arguments
 * but are not yet referenced directly from the index expression.
 * Instead, they are still referenced through parameters encoding
 * nested accesses.
 *
 * In particular, if "expr" is a read access, then check the arguments
 * starting at "first" to see if "expr" accesses a subset of
 * the elements accessed by the argument, or under more restrictive conditions.
 * If so, then this nested access can be removed from the constraints
 * governing the outer access.  There is no point in restricting
 * accesses to an array if in order to evaluate the restriction,
 * we have to access the same elements (or more).
 *
 * Rather than removing the argument at this point (which would
 * complicate the resolution of the other nested accesses), we simply
 * mark it here by replacing it by a NaN pet_expr.
 * These NaNs are then later removed in remove_marked_self_dependences.
 */
static __isl_give pet_expr *mark_self_dependences(__isl_take pet_expr *expr,
	int first)
{
	int i, n;

	if (pet_expr_access_is_write(expr))
		return expr;

	n = pet_expr_get_n_arg(expr);
	for (i = first; i < n; ++i) {
		int mark;
		pet_expr *arg;

		arg = pet_expr_get_arg(expr, i);
		mark = is_sub_access(expr, arg, first);
		pet_expr_free(arg);
		if (mark < 0)
			return pet_expr_free(expr);
		if (!mark)
			continue;

		arg = pet_expr_new_int(isl_val_nan(pet_expr_get_ctx(expr)));
		expr = pet_expr_set_arg(expr, i, arg);
	}

	return expr;
}

/* Is "expr" a NaN integer expression?
 */
static int expr_is_nan(__isl_keep pet_expr *expr)
{
	isl_val *v;
	int is_nan;

	if (pet_expr_get_type(expr) != pet_expr_int)
		return 0;

	v = pet_expr_int_get_val(expr);
	is_nan = isl_val_is_nan(v);
	isl_val_free(v);

	return is_nan;
}

/* Check if we have marked any self dependences (as NaNs)
 * in mark_self_dependences and remove them here.
 * It is safe to project them out since these arguments
 * can at most be referenced from the condition of the access relation,
 * but do not appear in the index expression.
 * "dim" is the dimension of the iteration domain.
 */
static __isl_give pet_expr *remove_marked_self_dependences(
	__isl_take pet_expr *expr, int dim, int first)
{
	int i, n;

	n = pet_expr_get_n_arg(expr);
	for (i = n - 1; i >= first; --i) {
		int is_nan;
		pet_expr *arg;

		arg = pet_expr_get_arg(expr, i);
		is_nan = expr_is_nan(arg);
		pet_expr_free(arg);
		if (!is_nan)
			continue;
		expr = pet_expr_access_project_out_arg(expr, dim, i);
	}

	return expr;
}

/* Look for parameters in any access relation in "expr" that
 * refer to nested accesses.  In particular, these are
 * parameters with name "__pet_expr".
 *
 * If there are any such parameters, then the domain of the index
 * expression and the access relation, which is either [] or
 * [[] -> [a_1,...,a_m]] at this point, is replaced by [[] -> [t_1,...,t_n]] or
 * [[] -> [a_1,...,a_m,t_1,...,t_n]], with m the original number of arguments
 * (n_arg) and n the number of these parameters
 * (after identifying identical nested accesses).
 *
 * This transformation is performed in several steps.
 * We first extract the arguments in pet_expr_extract_nested.
 * param2pos maps the original parameter position to the position
 * of the argument beyond the initial (n_arg) number of arguments.
 * Then we move these parameters to input dimensions.
 * t2pos maps the positions of these temporary input dimensions
 * to the positions of the corresponding arguments.
 * Finally, we express these temporary dimensions in terms of the domain
 * [[] -> [a_1,...,a_m,t_1,...,t_n]] and precompose index expression and access
 * relations with this function.
 */
__isl_give pet_expr *pet_expr_resolve_nested(__isl_take pet_expr *expr)
{
	int i, n, n_arg;
	int nparam;
	isl_ctx *ctx;
	isl_space *space;
	isl_local_space *ls;
	isl_aff *aff;
	isl_multi_aff *ma;
	int *param2pos;
	int *t2pos;

	if (!expr)
		return expr;

	n_arg = pet_expr_get_n_arg(expr);
	for (i = 0; i < n_arg; ++i) {
		pet_expr *arg;
		arg = pet_expr_get_arg(expr, i);
		arg = pet_expr_resolve_nested(arg);
		expr = pet_expr_set_arg(expr, i, arg);
	}

	if (pet_expr_get_type(expr) != pet_expr_access)
		return expr;

	space = pet_expr_access_get_parameter_space(expr);
	n = pet_nested_n_in_space(space);
	isl_space_free(space);
	if (n == 0)
		return expr;

	expr = pet_expr_access_align_params(expr);
	if (!expr)
		return NULL;

	space = pet_expr_access_get_parameter_space(expr);
	nparam = isl_space_dim(space, isl_dim_param);
	isl_space_free(space);

	ctx = pet_expr_get_ctx(expr);

	param2pos = isl_alloc_array(ctx, int, nparam);
	t2pos = isl_alloc_array(ctx, int, n);
	if (!param2pos)
		goto error;
	expr = pet_expr_extract_nested(expr, n, param2pos);
	expr = mark_self_dependences(expr, n_arg);
	if (!expr)
		goto error;

	n = 0;
	space = pet_expr_access_get_parameter_space(expr);
	nparam = isl_space_dim(space, isl_dim_param);
	for (i = nparam - 1; i >= 0; --i) {
		isl_id *id = isl_space_get_dim_id(space, isl_dim_param, i);
		if (!pet_nested_in_id(id)) {
			isl_id_free(id);
			continue;
		}

		expr = pet_expr_access_move_dims(expr,
				    isl_dim_in, n_arg + n, isl_dim_param, i, 1);
		t2pos[n] = n_arg + param2pos[i];
		n++;

		isl_id_free(id);
	}
	isl_space_free(space);

	space = pet_expr_access_get_parameter_space(expr);
	space = isl_space_set_from_params(space);
	space = isl_space_add_dims(space, isl_dim_set,
					pet_expr_get_n_arg(expr));
	space = isl_space_wrap(isl_space_from_range(space));
	ls = isl_local_space_from_space(isl_space_copy(space));
	space = isl_space_from_domain(space);
	space = isl_space_add_dims(space, isl_dim_out, n_arg + n);
	ma = isl_multi_aff_zero(space);

	for (i = 0; i < n_arg; ++i) {
		aff = isl_aff_var_on_domain(isl_local_space_copy(ls),
					    isl_dim_set, i);
		ma = isl_multi_aff_set_aff(ma, i, aff);
	}
	for (i = 0; i < n; ++i) {
		aff = isl_aff_var_on_domain(isl_local_space_copy(ls),
					    isl_dim_set, t2pos[i]);
		ma = isl_multi_aff_set_aff(ma, n_arg + i, aff);
	}
	isl_local_space_free(ls);

	expr = pet_expr_access_pullback_multi_aff(expr, ma);

	expr = remove_marked_self_dependences(expr, 0, n_arg);

	free(t2pos);
	free(param2pos);
	return expr;
error:
	free(t2pos);
	free(param2pos);
	return pet_expr_free(expr);
}
