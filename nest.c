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
