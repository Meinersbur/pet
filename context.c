/*
 * Copyright 2011      Leiden University. All rights reserved.
 * Copyright 2014      Ecole Normale Superieure. All rights reserved.
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

#include <isl/aff.h>

#include "aff.h"
#include "array.h"
#include "context.h"
#include "expr.h"
#include "expr_arg.h"
#include "nest.h"
#include "tree.h"

/* A pet_context represents the context in which a pet_expr
 * in converted to an affine expression.
 *
 * "domain" prescribes the domain of the affine expressions.
 *
 * "assignments" maps variable names to their currently known values.
 * Internally, the domains of the values may be equal to some prefix
 * of the space of "domain", but the domains are updated to be
 * equal to the space of "domain" before passing them to the user.
 *
 * If "allow_nested" is set, then the affine expression created
 * in this context may involve new parameters that encode a pet_expr.
 */
struct pet_context {
	int ref;

	isl_set *domain;
	isl_id_to_pw_aff *assignments;
	int allow_nested;
};

/* Create a pet_context with the given domain, assignments,
 * and value for allow_nested.
 */
static __isl_give pet_context *context_alloc(__isl_take isl_set *domain,
	__isl_take isl_id_to_pw_aff *assignments, int allow_nested)
{
	pet_context *pc;

	if (!domain || !assignments)
		goto error;

	pc = isl_calloc_type(isl_set_get_ctx(domain), struct pet_context);
	if (!pc)
		goto error;

	pc->ref = 1;
	pc->domain = domain;
	pc->assignments = assignments;
	pc->allow_nested = allow_nested;

	return pc;
error:
	isl_set_free(domain);
	isl_id_to_pw_aff_free(assignments);
	return NULL;
}

/* Create a pet_context with the given domain.
 *
 * Initially, there are no assigned values and parameters that
 * encode a pet_expr are not allowed.
 */
__isl_give pet_context *pet_context_alloc(__isl_take isl_set *domain)
{
	isl_id_to_pw_aff *assignments;

	if (!domain)
		return NULL;

	assignments = isl_id_to_pw_aff_alloc(isl_set_get_ctx(domain), 0);;
	return context_alloc(domain, assignments, 0);
}

/* Return an independent duplicate of "pc".
 */
static __isl_give pet_context *pet_context_dup(__isl_keep pet_context *pc)
{
	pet_context *dup;

	if (!pc)
		return NULL;

	dup = context_alloc(isl_set_copy(pc->domain),
			    isl_id_to_pw_aff_copy(pc->assignments),
			    pc->allow_nested);

	return dup;
}

/* Return a pet_context that is equal to "pc" and that has only one reference.
 */
static __isl_give pet_context *pet_context_cow(__isl_take pet_context *pc)
{
	if (!pc)
		return NULL;

	if (pc->ref == 1)
		return pc;
	pc->ref--;
	return pet_context_dup(pc);
}

/* Return an extra reference to "pc".
 */
__isl_give pet_context *pet_context_copy(__isl_keep pet_context *pc)
{
	if (!pc)
		return NULL;

	pc->ref++;
	return pc;
}

/* Free a reference to "pc" and return NULL.
 */
__isl_null pet_context *pet_context_free(__isl_take pet_context *pc)
{
	if (!pc)
		return NULL;
	if (--pc->ref > 0)
		return NULL;

	isl_set_free(pc->domain);
	isl_id_to_pw_aff_free(pc->assignments);
	free(pc);
	return NULL;
}

/* Return the isl_ctx in which "pc" was created.
 */
isl_ctx *pet_context_get_ctx(__isl_keep pet_context *pc)
{
	return pc ? isl_set_get_ctx(pc->domain) : NULL;
}

/* Return the domain of "pc".
 */
__isl_give isl_set *pet_context_get_domain(__isl_keep pet_context *pc)
{
	if (!pc)
		return NULL;
	return isl_set_copy(pc->domain);
}

/* Return the domain of "pc" in a form that is suitable
 * for use as a gist context.
 * In particular, remove all references to nested expression parameters
 * so that they do not get introduced in the gisted expression.
 */
__isl_give isl_set *pet_context_get_gist_domain(__isl_keep pet_context *pc)
{
	isl_set *domain;

	domain = pet_context_get_domain(pc);
	domain = pet_nested_remove_from_set(domain);
	return domain;
}

/* Return the domain space of "pc".
 *
 * The domain of "pc" may have constraints involving parameters
 * that encode a pet_expr.  These parameters are not relevant
 * outside this domain.  Furthermore, they need to be resolved
 * from the final result, so we do not want to propagate them needlessly.
 */
__isl_give isl_space *pet_context_get_space(__isl_keep pet_context *pc)
{
	isl_space *space;

	if (!pc)
		return NULL;

	space = isl_set_get_space(pc->domain);
	space = pet_nested_remove_from_space(space);
	return space;
}

/* Return the dimension of the domain space of "pc".
 */
unsigned pet_context_dim(__isl_keep pet_context *pc)
{
	if (!pc)
		return 0;
	return isl_set_dim(pc->domain, isl_dim_set);
}

/* Return the assignments of "pc".
 */
__isl_give isl_id_to_pw_aff *pet_context_get_assignments(
	__isl_keep pet_context *pc)
{
	if (!pc)
		return NULL;
	return isl_id_to_pw_aff_copy(pc->assignments);
}

/* Is "id" assigned any value in "pc"?
 */
int pet_context_is_assigned(__isl_keep pet_context *pc, __isl_keep isl_id *id)
{
	if (!pc || !id)
		return -1;
	return isl_id_to_pw_aff_has(pc->assignments, id);
}

/* Return the value assigned to "id" in "pc".
 *
 * Some dimensions may have been added to pc->domain after the value
 * associated to "id" was added.  We therefore need to adjust the domain
 * of the stored value to match pc->domain by adding the missing
 * dimensions.
 */
__isl_give isl_pw_aff *pet_context_get_value(__isl_keep pet_context *pc,
	__isl_take isl_id *id)
{
	int dim;
	isl_pw_aff *pa;
	isl_multi_aff *ma;

	if (!pc || !id)
		goto error;

	pa = isl_id_to_pw_aff_get(pc->assignments, id);
	dim = isl_pw_aff_dim(pa, isl_dim_in);
	if (dim == isl_set_dim(pc->domain, isl_dim_set))
		return pa;

	ma = pet_prefix_projection(pet_context_get_space(pc), dim);
	pa = isl_pw_aff_pullback_multi_aff(pa, ma);

	return pa;
error:
	isl_id_free(id);
	return NULL;
}

/* Assign the value "value" to "id" in "pc", replacing the previously
 * assigned value, if any.
 */
__isl_give pet_context *pet_context_set_value(__isl_take pet_context *pc,
	__isl_take isl_id *id, isl_pw_aff *value)
{
	pc = pet_context_cow(pc);
	if (!pc)
		goto error;
	pc->assignments = isl_id_to_pw_aff_set(pc->assignments, id, value);
	if (!pc->assignments)
		return pet_context_free(pc);
	return pc;
error:
	isl_id_free(id);
	isl_pw_aff_free(value);
	return NULL;
}

/* Remove any assignment to "id" in "pc".
 */
__isl_give pet_context *pet_context_clear_value(__isl_keep pet_context *pc,
	__isl_take isl_id *id)
{
	pc = pet_context_cow(pc);
	if (!pc)
		goto error;
	pc->assignments = isl_id_to_pw_aff_drop(pc->assignments, id);
	if (!pc->assignments)
		return pet_context_free(pc);
	return pc;
error:
	isl_id_free(id);
	return NULL;
}

/* Are affine expressions created in this context allowed to involve
 * parameters that encode a pet_expr?
 */
int pet_context_allow_nesting(__isl_keep pet_context *pc)
{
	if (!pc)
		return -1;
	return pc->allow_nested;
}

/* Allow affine expressions created in this context to involve
 * parameters that encode a pet_expr based on the value of "allow_nested".
 */
__isl_give pet_context *pet_context_set_allow_nested(__isl_take pet_context *pc,
	int allow_nested)
{
	if (!pc)
		return NULL;
	if (pc->allow_nested == allow_nested)
		return pc;
	pc = pet_context_cow(pc);
	if (!pc)
		return NULL;
	pc->allow_nested = allow_nested;
	return pc;
}

/* If the access expression "expr" writes to a (non-virtual) scalar,
 * then remove any assignment to the scalar in "pc".
 */
static int clear_write(__isl_keep pet_expr *expr, void *user)
{
	isl_id *id;
	pet_context **pc = (pet_context **) user;

	if (!pet_expr_access_is_write(expr))
		return 0;
	if (!pet_expr_is_scalar_access(expr))
		return 0;

	id = pet_expr_access_get_id(expr);
	if (isl_id_get_user(id))
		*pc = pet_context_clear_value(*pc, id);
	else
		isl_id_free(id);

	return 0;
}

/* Look for any writes to scalar variables in "expr" and
 * remove any assignment to them in "pc".
 */
__isl_give pet_context *pet_context_clear_writes_in_expr(
	__isl_take pet_context *pc, __isl_keep pet_expr *expr)
{
	if (pet_expr_foreach_access_expr(expr, &clear_write, &pc) < 0)
		pc = pet_context_free(pc);

	return pc;
}

/* Look for any writes to scalar variables in "tree" and
 * remove any assignment to them in "pc".
 */
__isl_give pet_context *pet_context_clear_writes_in_tree(
	__isl_take pet_context *pc, __isl_keep pet_tree *tree)
{
	if (pet_tree_foreach_access_expr(tree, &clear_write, &pc) < 0)
		pc = pet_context_free(pc);

	return pc;
}

/* Internal data structure for pet_context_add_parameters.
 *
 * "pc" is the context that is being updated.
 * "get_array_size" is a callback function that can be used to determine
 * the size of the array that is accessed by a given access expression.
 * "user" is the user data for this callback.
 */
struct pet_context_add_parameter_data {
	pet_context *pc;
	__isl_give pet_expr *(*get_array_size)(__isl_keep pet_expr *access,
		void *user);
	void *user;
};

/* Given an access expression "expr", add a parameter assignment to data->pc
 * to the variable being accessed, provided it is a read from an integer
 * scalar variable.
 * If an array is being accesed, then recursively call the function
 * on each of the access expressions in the size expression of the array.
 */
static int add_parameter(__isl_keep pet_expr *expr, void *user)
{
	struct pet_context_add_parameter_data *data = user;
	int pos;
	isl_id *id;
	isl_space *space;
	isl_local_space *ls;
	isl_aff *aff;
	isl_pw_aff *pa;

	if (!pet_expr_is_scalar_access(expr)) {
		pet_expr *size = data->get_array_size(expr, data->user);
		if (pet_expr_foreach_access_expr(size,
						&add_parameter, data) < 0)
			data->pc = pet_context_free(data->pc);
		pet_expr_free(size);
		return 0;
	}
	if (!pet_expr_access_is_read(expr))
		return 0;
	if (pet_expr_get_type_size(expr) == 0)
		return 0;

	id = pet_expr_access_get_id(expr);
	if (pet_context_is_assigned(data->pc, id)) {
		isl_id_free(id);
		return 0;
	}

	space = pet_context_get_space(data->pc);
	pos = isl_space_find_dim_by_id(space, isl_dim_param, id);
	if (pos < 0) {
		pos = isl_space_dim(space, isl_dim_param);
		space = isl_space_add_dims(space, isl_dim_param, 1);
		space = isl_space_set_dim_id(space, isl_dim_param, pos,
						isl_id_copy(id));
	}

	ls = isl_local_space_from_space(space);
	aff = isl_aff_var_on_domain(ls, isl_dim_param, pos);
	pa = isl_pw_aff_from_aff(aff);
	data->pc = pet_context_set_value(data->pc, id, pa);

	return 0;
}

/* Add an assignment to "pc" for each parameter in "tree".
 * "get_array_size" is a callback function that can be used to determine
 * the size of the array that is accessed by a given access expression.
 *
 * We initially treat as parameters any integer variable that is read
 * anywhere in "tree" or in any of the size expressions for any of
 * the arrays accessed in "tree".
 * Then we remove from those variables that are written anywhere
 * inside "tree".
 */
__isl_give pet_context *pet_context_add_parameters(__isl_take pet_context *pc,
	__isl_keep pet_tree *tree,
	__isl_give pet_expr *(*get_array_size)(__isl_keep pet_expr *access,
		void *user), void *user)
{
	struct pet_context_add_parameter_data data;

	data.pc = pc;
	data.get_array_size = get_array_size;
	data.user = user;
	if (pet_tree_foreach_access_expr(tree, &add_parameter, &data) < 0)
		data.pc = pet_context_free(data.pc);

	data.pc = pet_context_clear_writes_in_tree(data.pc, tree);

	return data.pc;
}

/* Given an access expression, check if it reads a scalar variable
 * that has a known value in "pc".
 * If so, then replace the access by an access to that value.
 */
static __isl_give pet_expr *access_plug_in_affine_read(
	__isl_take pet_expr *expr, void *user)
{
	pet_context *pc = user;
	isl_pw_aff *pa;

	if (pet_expr_access_is_write(expr))
		return expr;
	if (!pet_expr_is_scalar_access(expr))
		return expr;

	pa = pet_expr_extract_affine(expr, pc);
	if (!pa)
		return pet_expr_free(expr);
	if (isl_pw_aff_involves_nan(pa)) {
		isl_pw_aff_free(pa);
		return expr;
	}

	pet_expr_free(expr);
	expr = pet_expr_from_index(isl_multi_pw_aff_from_pw_aff(pa));

	return expr;
}

/* Replace every read access in "expr" to a scalar variable
 * that has a known value in "pc" by that known value.
 */
static __isl_give pet_expr *plug_in_affine_read(__isl_take pet_expr *expr,
	__isl_keep pet_context *pc)
{
	return pet_expr_map_access(expr, &access_plug_in_affine_read, pc);
}

/* Add an extra affine expression to "mpa" that is equal to
 * an extra dimension in the range of the wrapped relation in the domain
 * of "mpa".  "n_arg" is the original number of dimensions in this range.
 *
 * That is, if "n_arg" is 0, then the input has the form
 *
 *	D(i) -> [f(i)]
 *
 * and the output has the form
 *
 *	[D(i) -> [y]] -> [f(i), y]
 *
 * If "n_arg" is different from 0, then the input has the form
 *
 *	[D(i) -> [x]] -> [f(i,x)]
 *
 * with x consisting of "n_arg" dimensions, and the output has the form
 *
 *	[D(i) -> [x,y]] -> [f(i,x), y]
 *
 *
 * We first adjust the domain of "mpa" and then add the extra
 * affine expression (y).
 */
static __isl_give isl_multi_pw_aff *add_arg(__isl_take isl_multi_pw_aff *mpa,
	int n_arg)
{
	int dim;
	isl_space *space;
	isl_multi_aff *ma;
	isl_multi_pw_aff *mpa2;

	if (n_arg == 0) {
		space = isl_space_domain(isl_multi_pw_aff_get_space(mpa));
		dim = isl_space_dim(space, isl_dim_set);
		space = isl_space_from_domain(space);
		space = isl_space_add_dims(space, isl_dim_set, 1);
		ma = isl_multi_aff_domain_map(space);
	} else {
		isl_multi_aff *ma2;;
		isl_space *dom, *ran;

		space = isl_space_domain(isl_multi_pw_aff_get_space(mpa));
		space = isl_space_unwrap(space);
		dom = isl_space_domain(isl_space_copy(space));
		dim = isl_space_dim(dom, isl_dim_set);
		ran = isl_space_range(space);
		ran = isl_space_add_dims(ran, isl_dim_set, 1);
		space = isl_space_map_from_set(dom);
		ma = isl_multi_aff_identity(space);
		ma2 = isl_multi_aff_project_out_map(ran, isl_dim_set, n_arg, 1);
		ma = isl_multi_aff_product(ma, ma2);
	}

	mpa = isl_multi_pw_aff_pullback_multi_aff(mpa, ma);
	space = isl_space_domain(isl_multi_pw_aff_get_space(mpa));
	ma = isl_multi_aff_project_out_map(space, isl_dim_set, 0, dim + n_arg);
	mpa2 = isl_multi_pw_aff_from_multi_aff(ma);
	mpa = isl_multi_pw_aff_flat_range_product(mpa, mpa2);

	return mpa;
}

/* Add the integer value from "arg" to "mpa".
 */
static __isl_give isl_multi_pw_aff *add_int(__isl_take isl_multi_pw_aff *mpa,
	__isl_take pet_expr *arg)
{
	isl_space *space;
	isl_val *v;
	isl_aff *aff;
	isl_multi_pw_aff *mpa_arg;

	v = pet_expr_int_get_val(arg);
	pet_expr_free(arg);

	space = isl_space_domain(isl_multi_pw_aff_get_space(mpa));
	aff = isl_aff_val_on_domain(isl_local_space_from_space(space), v);
	mpa_arg = isl_multi_pw_aff_from_pw_aff(isl_pw_aff_from_aff(aff));

	mpa = isl_multi_pw_aff_flat_range_product(mpa, mpa_arg);

	return mpa;
}

/* Add the affine expression from "arg" to "mpa".
 * "n_arg" is the number of dimensions in the range of the wrapped
 * relation in the domain of "mpa".
 */
static __isl_give isl_multi_pw_aff *add_aff(__isl_take isl_multi_pw_aff *mpa,
	int n_arg, __isl_take pet_expr *arg)
{
	isl_multi_pw_aff *mpa_arg;

	mpa_arg = pet_expr_access_get_index(arg);
	pet_expr_free(arg);

	if (n_arg > 0) {
		isl_space *space;
		isl_multi_aff *ma;

		space = isl_space_domain(isl_multi_pw_aff_get_space(mpa));
		space = isl_space_unwrap(space);
		ma = isl_multi_aff_domain_map(space);
		mpa_arg = isl_multi_pw_aff_pullback_multi_aff(mpa_arg, ma);
	}

	mpa = isl_multi_pw_aff_flat_range_product(mpa, mpa_arg);

	return mpa;
}

/* Given the data space "space1" of an index expression passed
 * to a function and the data space "space2" of the corresponding
 * array accessed in the function, construct and return the complete
 * data space from the perspective of the function call.
 * If add is set, then it is not the index expression with space "space1" itself
 * that is passed to the function, but its address.
 *
 * In the simplest case, no member accesses are involved and "add" is not set.
 * Let "space1" be of the form A[x] and "space2" of the form B[y].
 * Then the returned space is A[x,y].
 * That is, the dimension is the sum of the dimensions and the name
 * is that of "space1".
 * If "add" is set, then the final dimension of "space1" is the same
 * as the initial dimension of "space2" and the dimension of the result
 * is one less that the sum.  This also applies when the dimension
 * of "space1" is zero.  The dimension of "space2" can never be zero
 * when "add" is set since a pointer value is passed to the function,
 * which is treated as an array of dimension at least 1.
 *
 * If "space1" involves any member accesses, then it is the innermost
 * array space of "space1" that needs to be extended with "space2".
 * This innermost array space appears in the range of the wrapped
 * relation in "space1".
 *
 * If "space2" involves any member accesses, then it is the outermost
 * array space of "space2" that needs to be combined with innermost
 * array space of "space1".  This outermost array space appears
 * in the deepest nesting of the domains and is therefore handled
 * recursively.
 *
 * For example, if "space1" is of the form
 *
 *	s_a[s[x] -> a[y]]
 *
 * and "space2" is of the form
 *
 *	d_b_c[d_b[d[z] -> b[u]] -> c[v]]
 *
 * then the resulting space is
 *
 *	s_a_b_c[s_a_b[s_a[s[x] -> a[y,z]] -> b[u]] -> c[v]]
 */
static __isl_give isl_space *patch_space(__isl_take isl_space *space1,
	__isl_take isl_space *space2, int add)
{
	int dim;
	isl_id *id;

	if (!space1 || !space2)
		goto error;

	if (isl_space_is_wrapping(space2)) {
		isl_ctx *ctx;
		isl_space *dom;
		const char *name1, *name2;
		char *name;

		ctx = isl_space_get_ctx(space1);
		space2 = isl_space_unwrap(space2);
		dom = isl_space_domain(isl_space_copy(space2));
		space1 = patch_space(space1, dom, add);
		space2 = isl_space_range(space2);
		name1 = isl_space_get_tuple_name(space1, isl_dim_set);
		name2 = isl_space_get_tuple_name(space2, isl_dim_set);
		name = pet_array_member_access_name(ctx, name1, name2);
		space1 = isl_space_product(space1, space2);
		space1 = isl_space_set_tuple_name(space1, isl_dim_set, name);
		free(name);
		return space1;
	}

	dim = isl_space_dim(space2, isl_dim_set) - add;
	id = isl_space_get_tuple_id(space1, isl_dim_set);
	if (isl_space_is_wrapping(space1)) {
		isl_id *id;

		space1 = isl_space_unwrap(space1);
		id = isl_space_get_tuple_id(space1, isl_dim_out);
		space1 = isl_space_add_dims(space1, isl_dim_out, dim);
		space1 = isl_space_set_tuple_id(space1, isl_dim_out, id);
		space1 = isl_space_wrap(space1);
	} else {
		space1 = isl_space_add_dims(space1, isl_dim_out, dim);
	}
	space1 = isl_space_set_tuple_id(space1, isl_dim_set, id);

	isl_space_free(space2);
	return space1;
error:
	isl_space_free(space1);
	isl_space_free(space2);
	return NULL;
}

/* Drop the initial dimension of "map", assuming that it is equal to zero.
 * If it turns out not to be equal to zero, then drop the initial dimension
 * of "map" after setting the value to zero and print a warning.
 */
static __isl_give isl_map *drop_initial_zero(__isl_take isl_map *map,
	__isl_keep isl_map *prefix)
{
	isl_map *zeroed;

	zeroed = isl_map_copy(map);
	zeroed = isl_map_fix_si(zeroed, isl_dim_out, 0, 0);
	map = isl_map_subtract(map, isl_map_copy(zeroed));
	if (!isl_map_is_empty(map)) {
		fprintf(stderr, "possible out-of-bounds accesses\n");
		isl_map_dump(map);
		fprintf(stderr, "when passing\n");
		isl_map_dump(prefix);
	}
	isl_map_free(map);
	map = zeroed;
	map = isl_map_project_out(map, isl_dim_out, 0, 1);
	return map;
}

/* Given an identity mapping "id" that adds structure to
 * the range of "map" with dimensions "pos" and "pos + 1" replaced
 * by their sum, adjust "id" to apply to the range of "map" directly.
 * That is, plug in
 *
 *	[i_0, ..., i_pos, i_{pos+1}, i_{pos+2}, ...] ->
 *		[i_0, ..., i_pos + i_{pos+1}, i_{pos+2}, ...]
 *
 * in "id", where the domain of this mapping corresponds to the range
 * of "map" and the range of this mapping corresponds to the original
 * domain of "id".
 */
static __isl_give isl_map *patch_map_add(__isl_take isl_map *id,
	__isl_keep isl_map *map, int pos)
{
	isl_space *space;
	isl_multi_aff *ma;
	isl_aff *aff1, *aff2;

	space = isl_space_range(isl_map_get_space(map));
	ma = isl_multi_aff_identity(isl_space_map_from_set(space));
	aff1 = isl_multi_aff_get_aff(ma, pos);
	aff2 = isl_multi_aff_get_aff(ma, pos + 1);
	aff1 = isl_aff_add(aff1, aff2);
	ma = isl_multi_aff_set_aff(ma, pos, aff1);
	ma = isl_multi_aff_drop_dims(ma, isl_dim_out, pos + 1, 1);
	id = isl_map_preimage_domain_multi_aff(id, ma);

	return id;
}

/* Return the dimension of the innermost array in the data space "space".
 * If "space" is not a wrapping space, the it does not involve any
 * member accesses and the innermost array is simply the accessed
 * array itself.
 * Otherwise, the innermost array is encoded in the range of the
 * wrapped space.
 */
static int innermost_dim(__isl_keep isl_space *space)
{
	int dim;

	if (!isl_space_is_wrapping(space))
		return isl_space_dim(space, isl_dim_set);

	space = isl_space_copy(space);
	space = isl_space_unwrap(space);
	dim = isl_space_dim(space, isl_dim_out);
	isl_space_free(space);

	return dim;
}

/* Internal data structure for patch_map.
 *
 * "prefix" is the index expression passed to the function
 * "add" is set if it is the address of "prefix" that is passed to the function.
 * "res" collects the results.
 */
struct pet_patch_map_data {
	isl_map *prefix;
	int add;

	isl_union_map *res;
};

/* Combine the index expression data->prefix with the subaccess relation "map".
 * If data->add is set, then it is not the index expression data->prefix itself
 * that is passed to the function, but its address.
 *
 * If data->add is not set, then we essentially need to concatenate
 * data->prefix with map, except that we need to make sure that
 * the target space is set correctly.  This target space is computed
 * by the function patch_space.  We then simply compute the flat
 * range product and subsequently reset the target space.
 *
 * If data->add is set then the outer dimension of "map" is an offset
 * with respect to the inner dimension of data->prefix and we therefore
 * need to add these two dimensions rather than simply concatenating them.
 * This computation is performed in patch_map_add.
 * If however, the innermost accessed array of data->prefix is
 * zero-dimensional, then there is no innermost dimension of data->prefix
 * to add to the outermost dimension of "map",  Instead, we are passing
 * a pointer to a scalar member, meaning that the outermost dimension
 * of "map" needs to be zero and that this zero needs to be removed
 * from the concatenation.  This computation is performed in drop_initial_zero.
 */
static int patch_map(__isl_take isl_map *map, void *user)
{
	struct pet_patch_map_data *data = user;
	isl_space *space;
	isl_map *id;
	int pos, dim;

	space = isl_space_range(isl_map_get_space(data->prefix));
	dim = innermost_dim(space);
	pos = isl_space_dim(space, isl_dim_set) - dim;
	space = patch_space(space, isl_space_range(isl_map_get_space(map)),
				data->add);
	if (data->add && dim == 0)
		map = drop_initial_zero(map, data->prefix);
	map = isl_map_flat_range_product(isl_map_copy(data->prefix), map);
	space = isl_space_map_from_set(space);
	space = isl_space_add_dims(space, isl_dim_in, 0);
	id = isl_map_identity(space);
	if (data->add && dim != 0)
		id = patch_map_add(id, map, pos + dim - 1);
	map = isl_map_apply_range(map, id);
	data->res = isl_union_map_add_map(data->res, map);

	return 0;
}

/* Combine the index expression of "expr" with the subaccess relation "access".
 * If "add" is set, then it is not the index expression of "expr" itself
 * that is passed to the function, but its address.
 *
 * We call patch_map on each map in "access" and return the combined results.
 */
static __isl_give isl_union_map *patch(__isl_take isl_union_map *access,
	__isl_keep pet_expr *expr, int add)
{
	struct pet_patch_map_data data;
	isl_map *map;

	map = isl_map_from_multi_pw_aff(pet_expr_access_get_index(expr));
	map = isl_map_align_params(map, isl_union_map_get_space(access));
	access = isl_union_map_align_params(access, isl_map_get_space(map));
	data.prefix = map;
	data.add = add;
	data.res = isl_union_map_empty(isl_union_map_get_space(access));
	if (isl_union_map_foreach_map(access, &patch_map, &data) < 0)
		data.res = isl_union_map_free(data.res);
	isl_union_map_free(access);
	isl_map_free(data.prefix);

	return data.res;
}

/* Set the access relations of "expr", which appears in the argument
 * at position "pos" in a call expression by composing the access
 * relations in "summary" with the expression "int_arg" of the integer
 * arguments in terms of the domain and expression arguments of "expr" and
 * combining the result with the index expression passed to the function.
 * If "add" is set, then it is not "expr" itself that is passed
 * to the function, but the address of "expr".
 *
 * We reset the read an write flag of "expr" and rely on
 * pet_expr_access_set_access setting the flags based on
 * the access relations.
 *
 * After relating each access relation of the called function
 * to the domain and expression arguments at the call site,
 * the result is combined with the index expression by the function patch
 * and then stored in the access expression.
 */
static __isl_give pet_expr *set_access_relations(__isl_take pet_expr *expr,
	__isl_keep pet_function_summary *summary, int pos,
	__isl_take isl_multi_pw_aff *int_arg, int add)
{
	enum pet_expr_access_type type;

	expr = pet_expr_access_set_read(expr, 0);
	expr = pet_expr_access_set_write(expr, 0);
	for (type = pet_expr_access_begin; type < pet_expr_access_end; ++type) {
		isl_union_map *access;

		access = pet_function_summary_arg_get_access(summary,
								pos, type);
		access = isl_union_map_preimage_domain_multi_pw_aff(access,
						isl_multi_pw_aff_copy(int_arg));
		access = patch(access, expr, add);
		expr = pet_expr_access_set_access(expr, type, access);
	}
	isl_multi_pw_aff_free(int_arg);

	return expr;
}

/* Set the access relations of "arg", which appears in the argument
 * at position "pos" in the call expression "call" based on the
 * information in "summary".
 * If "add" is set, then it is not "arg" itself that is passed
 * to the function, but the address of "arg".
 *
 * We create an affine function "int_arg" that expresses
 * the integer function call arguments in terms of the domain of "arg"
 * (i.e., the outer loop iterators) and the expression arguments.
 * If the actual argument is not an affine expression or if it itself
 * has expression arguments, then it is added as an argument to "arg" and
 * "int_arg" is made to reference this additional expression argument.
 *
 * Finally, we call set_access_relations to plug in the actual arguments
 * (expressed in "int_arg") into the access relations in "summary" and
 * to add the resulting access relations to "arg".
 */
static __isl_give pet_expr *access_plug_in_summary(__isl_take pet_expr *arg,
	__isl_keep pet_expr *call, __isl_keep pet_function_summary *summary,
	int pos, int add)
{
	int j, n;
	isl_space *space;
	isl_multi_pw_aff *int_arg;
	int arg_n_arg;

	space = pet_expr_access_get_augmented_domain_space(arg);
	space = isl_space_from_domain(space);
	arg_n_arg = pet_expr_get_n_arg(arg);
	int_arg = isl_multi_pw_aff_zero(space);
	n = pet_function_summary_get_n_arg(summary);
	for (j = 0; j < n; ++j) {
		pet_expr *arg_j;
		int arg_j_n_arg;

		if (!pet_function_summary_arg_is_int(summary, j))
			continue;

		arg_j = pet_expr_get_arg(call, j);
		arg_j_n_arg = pet_expr_get_n_arg(arg_j);
		if (pet_expr_get_type(arg_j) == pet_expr_int) {
			int_arg = add_int(int_arg, arg_j);
		} else if (arg_j_n_arg != 0 || !pet_expr_is_affine(arg_j)) {
			arg = pet_expr_insert_arg(arg, arg_n_arg,
							arg_j);
			int_arg = add_arg(int_arg, arg_n_arg);
			arg_n_arg++;
		} else {
			int_arg = add_aff(int_arg, arg_n_arg, arg_j);
		}
	}
	arg = set_access_relations(arg, summary, pos, int_arg, add);

	return arg;
}

/* Given the argument "arg" at position "pos" of "call",
 * check if it is either an access expression or the address
 * of an access expression.  If so, use the information in "summary"
 * to set the access relations of the access expression.
 */
static __isl_give pet_expr *arg_plug_in_summary(__isl_take pet_expr *arg,
	__isl_keep pet_expr *call, __isl_keep pet_function_summary *summary,
	int pos)
{
	enum pet_expr_type type;
	pet_expr *arg2;

	type = pet_expr_get_type(arg);
	if (type == pet_expr_access)
		return access_plug_in_summary(arg, call, summary, pos, 0);
	if (type != pet_expr_op)
		return arg;
	if (pet_expr_op_get_type(arg) != pet_op_address_of)
		return arg;

	arg2 = pet_expr_get_arg(arg, 0);
	if (pet_expr_get_type(arg2) == pet_expr_access)
		arg2 = access_plug_in_summary(arg2, call, summary, pos, 1);
	arg = pet_expr_set_arg(arg, 0, arg2);

	return arg;
}

/* Given a call expression, check if the integer arguments can
 * be represented by affine expressions in the context "pc"
 * (assuming they are not already affine expressions).
 * If so, replace these arguments by the corresponding affine expressions.
 */
static __isl_give pet_expr *call_plug_in_affine_args(__isl_take pet_expr *call,
	__isl_keep pet_context *pc)
{
	int i, n;

	n = pet_expr_get_n_arg(call);
	for (i = 0; i < n; ++i) {
		pet_expr *arg;
		isl_pw_aff *pa;

		arg = pet_expr_get_arg(call, i);
		if (!arg)
			return pet_expr_free(call);
		if (pet_expr_get_type_size(arg) == 0 ||
		    pet_expr_is_affine(arg)) {
			pet_expr_free(arg);
			continue;
		}

		pa = pet_expr_extract_affine(arg, pc);
		pet_expr_free(arg);
		if (!pa)
			return pet_expr_free(call);
		if (isl_pw_aff_involves_nan(pa)) {
			isl_pw_aff_free(pa);
			continue;
		}

		arg = pet_expr_from_index(isl_multi_pw_aff_from_pw_aff(pa));
		call = pet_expr_set_arg(call, i, arg);
	}

	return call;
}

/* If "call" has an associated function summary, then use it
 * to set the access relations of the array arguments of the function call.
 *
 * We first plug in affine expressions for the integer arguments
 * whenever possible as these arguments will be plugged in
 * in the access relations of the array arguments.
 */
static __isl_give pet_expr *call_plug_in_summary(__isl_take pet_expr *call,
	void *user)
{
	pet_context *pc = user;
	pet_function_summary *summary;
	int i, n;

	if (!pet_expr_call_has_summary(call))
		return call;

	call = call_plug_in_affine_args(call, pc);

	summary = pet_expr_call_get_summary(call);
	if (!summary)
		return pet_expr_free(call);

	n = pet_expr_get_n_arg(call);
	for (i = 0; i < n; ++i) {
		pet_expr *arg_i;

		if (!pet_function_summary_arg_is_array(summary, i))
			continue;

		arg_i = pet_expr_get_arg(call, i);
		arg_i = arg_plug_in_summary(arg_i, call, summary, i);
		call = pet_expr_set_arg(call, i, arg_i);
	}

	pet_function_summary_free(summary);
	return call;
}

/* For each call subexpression of "expr", plug in the access relations
 * from the associated function summary (if any).
 */
static __isl_give pet_expr *plug_in_summaries(__isl_take pet_expr *expr,
	__isl_keep pet_context *pc)
{
	return pet_expr_map_call(expr, &call_plug_in_summary, pc);
}

/* Evaluate "expr" in the context of "pc".
 *
 * In particular, we first make sure that all the access expressions
 * inside "expr" have the same domain as "pc".
 * Then, we plug in affine expressions for scalar reads,
 * plug in the arguments of all access expressions in "expr" and
 * plug in the access relations from the summary functions associated
 * to call expressions.
 */
__isl_give pet_expr *pet_context_evaluate_expr(__isl_keep pet_context *pc,
	__isl_take pet_expr *expr)
{
	expr = pet_expr_insert_domain(expr, pet_context_get_space(pc));
	expr = plug_in_affine_read(expr, pc);
	expr = pet_expr_plug_in_args(expr, pc);
	expr = plug_in_summaries(expr, pc);
	return expr;
}

/* Wrapper around pet_context_evaluate_expr
 * for use as a callback to pet_tree_map_expr.
 */
static __isl_give pet_expr *evaluate_expr(__isl_take pet_expr *expr,
	void *user)
{
	pet_context *pc = user;

	return pet_context_evaluate_expr(pc, expr);
}

/* Evaluate "tree" in the context of "pc".
 * That is, evaluate all the expressions of "tree" in the context of "pc".
 */
__isl_give pet_tree *pet_context_evaluate_tree(__isl_keep pet_context *pc,
	__isl_take pet_tree *tree)
{
	return pet_tree_map_expr(tree, &evaluate_expr, pc);
}

/* Add an unbounded inner dimension "id" to pc->domain.
 *
 * The assignments are not adjusted here and therefore keep
 * their original domain.  These domains need to be adjusted before
 * these assigned values can be used.  This is taken care of by
 * pet_context_get_value.
 */
static __isl_give pet_context *extend_domain(__isl_take pet_context *pc,
	__isl_take isl_id *id)
{
	int pos;

	pc = pet_context_cow(pc);
	if (!pc || !id)
		goto error;

	pos = pet_context_dim(pc);
	pc->domain = isl_set_add_dims(pc->domain, isl_dim_set, 1);
	pc->domain = isl_set_set_dim_id(pc->domain, isl_dim_set, pos, id);
	if (!pc->domain)
		return pet_context_free(pc);

	return pc;
error:
	pet_context_free(pc);
	isl_id_free(id);
	return NULL;
}

/* Add an unbounded inner iterator "id" to pc->domain.
 * Additionally, mark the variable "id" as having the value of this
 * new inner iterator.
 */
__isl_give pet_context *pet_context_add_inner_iterator(
	__isl_take pet_context *pc, __isl_take isl_id *id)
{
	int pos;
	isl_space *space;
	isl_local_space *ls;
	isl_aff *aff;
	isl_pw_aff *pa;

	if (!pc || !id)
		goto error;

	pos = pet_context_dim(pc);
	pc = extend_domain(pc, isl_id_copy(id));
	if (!pc)
		goto error;

	space = pet_context_get_space(pc);
	ls = isl_local_space_from_space(space);
	aff = isl_aff_var_on_domain(ls, isl_dim_set, pos);
	pa = isl_pw_aff_from_aff(aff);

	pc = pet_context_set_value(pc, id, pa);

	return pc;
error:
	pet_context_free(pc);
	isl_id_free(id);
	return NULL;
}

/* Add an inner iterator to pc->domain.
 * In particular, extend the domain with an inner loop { [t] : t >= 0 }.
 */
__isl_give pet_context *pet_context_add_infinite_loop(
	__isl_take pet_context *pc)
{
	int dim;
	isl_ctx *ctx;
	isl_id *id;

	if (!pc)
		return NULL;

	dim = pet_context_dim(pc);
	ctx = pet_context_get_ctx(pc);
	id = isl_id_alloc(ctx, "t", NULL);
	pc = extend_domain(pc, id);
	pc = pet_context_cow(pc);
	if (!pc)
		return NULL;
	pc->domain = isl_set_lower_bound_si(pc->domain, isl_dim_set, dim, 0);
	if (!pc->domain)
		return pet_context_free(pc);

	return pc;
}

/* Internal data structure for preimage_domain.
 *
 * "ma" is the function under which the preimage should be computed.
 * "assignments" collects the results.
 */
struct pet_preimage_domain_data {
	isl_multi_aff *ma;
	isl_id_to_pw_aff *assignments;
};

/* Add the assignment to "key" of the preimage of "val" under data->ma
 * to data->assignments.
 *
 * Some dimensions may have been added to the domain of the enclosing
 * pet_context after the value "val" was added.  We therefore need to
 * adjust the domain of "val" to match the range of data->ma (which
 * in turn matches the domain of the pet_context), by adding the missing
 * dimensions.
 */
static int preimage_domain_pair(__isl_take isl_id *key,
	__isl_take isl_pw_aff *val, void *user)
{
	struct pet_preimage_domain_data *data = user;
	int dim;
	isl_multi_aff *ma;

	ma = isl_multi_aff_copy(data->ma);

	dim = isl_pw_aff_dim(val, isl_dim_in);
	if (dim != isl_multi_aff_dim(data->ma, isl_dim_out)) {
		isl_space *space;
		isl_multi_aff *proj;
		space = isl_multi_aff_get_space(data->ma);
		space = isl_space_range(space);
		proj = pet_prefix_projection(space, dim);
		ma = isl_multi_aff_pullback_multi_aff(proj, ma);
	}

	val = isl_pw_aff_pullback_multi_aff(val, ma);
	data->assignments = isl_id_to_pw_aff_set(data->assignments, key, val);

	return 0;
}

/* Compute the preimage of "assignments" under the function represented by "ma".
 * In other words, plug in "ma" in the domains of the assigned values.
 */
static __isl_give isl_id_to_pw_aff *preimage_domain(
	__isl_take isl_id_to_pw_aff *assignments, __isl_keep isl_multi_aff *ma)
{
	struct pet_preimage_domain_data data = { ma };
	isl_ctx *ctx;

	ctx = isl_id_to_pw_aff_get_ctx(assignments);
	data.assignments = isl_id_to_pw_aff_alloc(ctx, 0);
	if (isl_id_to_pw_aff_foreach(assignments, &preimage_domain_pair,
					&data) < 0)
		data.assignments = isl_id_to_pw_aff_free(data.assignments);
	isl_id_to_pw_aff_free(assignments);

	return data.assignments;
}

/* Compute the preimage of "pc" under the function represented by "ma".
 * In other words, plug in "ma" in the domain of "pc".
 */
__isl_give pet_context *pet_context_preimage_domain(__isl_take pet_context *pc,
	__isl_keep isl_multi_aff *ma)
{
	pc = pet_context_cow(pc);
	if (!pc)
		return NULL;
	pc->domain = isl_set_preimage_multi_aff(pc->domain,
						isl_multi_aff_copy(ma));
	pc->assignments = preimage_domain(pc->assignments, ma);
	if (!pc->domain || !pc->assignments)
		return pet_context_free(pc);
	return pc;
}

/* Add the constraints of "set" to the domain of "pc".
 */
__isl_give pet_context *pet_context_intersect_domain(__isl_take pet_context *pc,
	__isl_take isl_set *set)
{
	pc = pet_context_cow(pc);
	if (!pc)
		goto error;
	pc->domain = isl_set_intersect(pc->domain, set);
	if (!pc->domain)
		return pet_context_free(pc);
	return pc;
error:
	pet_context_free(pc);
	isl_set_free(set);
	return NULL;
}

void pet_context_dump(__isl_keep pet_context *pc)
{
	if (!pc)
		return;
	fprintf(stderr, "domain: ");
	isl_set_dump(pc->domain);
	fprintf(stderr, "assignments: ");
	isl_id_to_pw_aff_dump(pc->assignments);
	fprintf(stderr, "nesting allowed: %d\n", pc->allow_nested);
}
