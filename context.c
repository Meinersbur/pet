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
#include "context.h"
#include "expr.h"
#include "expr_arg.h"
#include "nest.h"

/* A pet_context represents the context in which a pet_expr
 * in converted to an affine expression.
 *
 * "domain" prescribes the domain of the affine expressions.
 *
 * "assignments" maps variable names to their currently known values.
 * Internally, the domains of the values may be equal to some prefix
 * of the space of "domain", but the domains are updated to be
 * equal to the space of "domain" before passing them to the user.
 * If a variable has been assigned an unknown value (possibly because
 * it may be assigned a different expression in each iteration) or a value
 * that is not an affine expression, then the corresponding isl_pw_aff
 * is set to NaN.
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

/* Return a piecewise affine expression defined on the specified domain
 * that represents NaN.
 */
static __isl_give isl_pw_aff *nan_on_domain(__isl_take isl_space *space)
{
	return isl_pw_aff_nan_on_domain(isl_local_space_from_space(space));
}

/* Assign the value NaN to "id" in "pc", marked it as having an unknown
 * value.
 */
__isl_give pet_context *pet_context_mark_unknown(__isl_take pet_context *pc,
	__isl_take isl_id *id)
{
	isl_pw_aff *pa;

	pa = nan_on_domain(pet_context_get_space(pc));
	pc = pet_context_set_value(pc, id, pa);

	return pc;
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
 * then mark the scalar as having an unknown value in "pc".
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
		*pc = pet_context_mark_unknown(*pc, id);
	else
		isl_id_free(id);

	return 0;
}

/* Look for any writes to scalar variables in "expr" and
 * mark them as having an unknown value in "pc".
 */
__isl_give pet_context *pet_context_clear_writes_in_expr(
	__isl_take pet_context *pc, __isl_keep pet_expr *expr)
{
	if (pet_expr_foreach_access_expr(expr, &clear_write, &pc) < 0)
		pc = pet_context_free(pc);

	return pc;
}

/* Look for any writes to scalar variables in "tree" and
 * mark them as having an unknown value in "pc".
 */
__isl_give pet_context *pet_context_clear_writes_in_tree(
	__isl_take pet_context *pc, __isl_keep pet_tree *tree)
{
	if (pet_tree_foreach_access_expr(tree, &clear_write, &pc) < 0)
		pc = pet_context_free(pc);

	return pc;
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

/* Evaluate "expr" in the context of "pc".
 *
 * In particular, we first make sure that all the access expressions
 * inside "expr" have the same domain as "pc".
 * Then, we plug in affine expressions for scalar reads and
 * plug in the arguments of all access expressions in "expr".
 */
__isl_give pet_expr *pet_context_evaluate_expr(__isl_keep pet_context *pc,
	__isl_take pet_expr *expr)
{
	expr = pet_expr_insert_domain(expr, pet_context_get_space(pc));
	expr = plug_in_affine_read(expr, pc);
	return pet_expr_plug_in_args(expr, pc);
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
