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

#include <isl/id_to_pw_aff.h>

#include "aff.h"
#include "expr.h"
#include "expr_arg.h"
#include "nest.h"
#include "scop.h"
#include "skip.h"
#include "state.h"
#include "tree2scop.h"

/* Update "pc" by taking into account the writes in "stmt".
 * That is, first mark all scalar variables that are written by "stmt"
 * as having an unknown value.  Afterwards,
 * if "stmt" is a top-level (i.e., unconditional) assignment
 * to a scalar variable, then update "pc" accordingly.
 *
 * In particular, if the lhs of the assignment is a scalar variable, then mark
 * the variable as having been assigned.  If, furthermore, the rhs
 * is an affine expression, then keep track of this value in "pc"
 * so that we can plug it in when we later come across the same variable.
 *
 * We skip assignments to virtual arrays (those with NULL user pointer).
 */
static __isl_give pet_context *handle_writes(struct pet_stmt *stmt,
	__isl_take pet_context *pc)
{
	pet_expr *body = stmt->body;
	pet_expr *arg;
	isl_id *id;
	isl_pw_aff *pa;

	pc = pet_context_clear_writes_in_expr(pc, body);
	if (!pc)
		return NULL;

	if (pet_expr_get_type(body) != pet_expr_op)
		return pc;
	if (pet_expr_op_get_type(body) != pet_op_assign)
		return pc;
	if (!isl_set_plain_is_universe(stmt->domain))
		return pc;
	arg = pet_expr_get_arg(body, 0);
	if (!pet_expr_is_scalar_access(arg)) {
		pet_expr_free(arg);
		return pc;
	}

	id = pet_expr_access_get_id(arg);
	pet_expr_free(arg);

	if (!isl_id_get_user(id)) {
		isl_id_free(id);
		return pc;
	}

	arg = pet_expr_get_arg(body, 1);
	pa = pet_expr_extract_affine(arg, pc);
	pc = pet_context_mark_assigned(pc, isl_id_copy(id));
	pet_expr_free(arg);

	if (pa && isl_pw_aff_involves_nan(pa)) {
		isl_id_free(id);
		isl_pw_aff_free(pa);
		return pc;
	}

	pc = pet_context_set_value(pc, id, pa);

	return pc;
}

/* Update "pc" based on the write accesses (and, in particular,
 * assignments) in "scop".
 */
static __isl_give pet_context *scop_handle_writes(struct pet_scop *scop,
	__isl_take pet_context *pc)
{
	int i;

	if (!scop)
		return pet_context_free(pc);
	for (i = 0; i < scop->n_stmt; ++i)
		pc = handle_writes(scop->stmts[i], pc);

	return pc;
}

/* Convert a top-level pet_expr to a pet_scop with one statement
 * within the context "pc".
 * This mainly involves resolving nested expression parameters
 * and setting the name of the iteration space.
 * The name is given by "label" if it is non-NULL.  Otherwise,
 * it is of the form S_<stmt_nr>.
 * The location of the statement is set to "loc".
 */
static struct pet_scop *scop_from_expr(__isl_take pet_expr *expr,
	__isl_take isl_id *label, int stmt_nr, __isl_take pet_loc *loc,
	__isl_keep pet_context *pc)
{
	isl_ctx *ctx;
	struct pet_stmt *ps;

	ctx = pet_expr_get_ctx(expr);

	expr = pet_expr_plug_in_args(expr, pc);
	expr = pet_expr_resolve_nested(expr);
	expr = pet_expr_resolve_assume(expr, pc);
	ps = pet_stmt_from_pet_expr(loc, label, stmt_nr, expr);
	return pet_scop_from_pet_stmt(ctx, ps);
}

/* Construct a pet_scop with a single statement killing the entire
 * array "array".
 * The location of the statement is set to "loc".
 */
static struct pet_scop *kill(__isl_take pet_loc *loc, struct pet_array *array,
	__isl_keep pet_context *pc, struct pet_state *state)
{
	isl_ctx *ctx;
	isl_id *id;
	isl_space *space;
	isl_multi_pw_aff *index;
	isl_map *access;
	pet_expr *expr;
	struct pet_scop *scop;

	if (!array)
		goto error;
	ctx = isl_set_get_ctx(array->extent);
	access = isl_map_from_range(isl_set_copy(array->extent));
	id = isl_set_get_tuple_id(array->extent);
	space = isl_space_alloc(ctx, 0, 0, 0);
	space = isl_space_set_tuple_id(space, isl_dim_out, id);
	index = isl_multi_pw_aff_zero(space);
	expr = pet_expr_kill_from_access_and_index(access, index);
	return scop_from_expr(expr, NULL, state->n_stmt++, loc, pc);
error:
	pet_loc_free(loc);
	return NULL;
}

/* Construct and return a pet_array corresponding to the variable
 * accessed by "access" by calling the extract_array callback.
 */
static struct pet_array *extract_array(__isl_keep pet_expr *access,
	__isl_keep pet_context *pc, struct pet_state *state)
{
	return state->extract_array(access, pc, state->user);
}

/* Construct a pet_scop for a (single) variable declaration
 * within the context "pc".
 *
 * The scop contains the variable being declared (as an array)
 * and a statement killing the array.
 *
 * If the declaration comes with an initialization, then the scop
 * also contains an assignment to the variable.
 */
static struct pet_scop *scop_from_decl(__isl_keep pet_tree *tree,
	__isl_keep pet_context *pc, struct pet_state *state)
{
	int type_size;
	isl_ctx *ctx;
	struct pet_array *array;
	struct pet_scop *scop_decl, *scop;
	pet_expr *lhs, *rhs, *pe;

	array = extract_array(tree->u.d.var, pc, state);
	if (array)
		array->declared = 1;
	scop_decl = kill(pet_tree_get_loc(tree), array, pc, state);
	scop_decl = pet_scop_add_array(scop_decl, array);

	if (tree->type != pet_tree_decl_init)
		return scop_decl;

	lhs = pet_expr_copy(tree->u.d.var);
	rhs = pet_expr_copy(tree->u.d.init);
	type_size = pet_expr_get_type_size(lhs);
	pe = pet_expr_new_binary(type_size, pet_op_assign, lhs, rhs);
	scop = scop_from_expr(pe, NULL, state->n_stmt++,
				pet_tree_get_loc(tree), pc);

	scop_decl = pet_scop_prefix(scop_decl, 0);
	scop = pet_scop_prefix(scop, 1);

	ctx = pet_tree_get_ctx(tree);
	scop = pet_scop_add_seq(ctx, scop_decl, scop);

	return scop;
}

/* Embed the given iteration domain in an extra outer loop
 * with induction variable "var".
 * If this variable appeared as a parameter in the constraints,
 * it is replaced by the new outermost dimension.
 */
static __isl_give isl_set *embed(__isl_take isl_set *set,
	__isl_take isl_id *var)
{
	int pos;

	set = isl_set_insert_dims(set, isl_dim_set, 0, 1);
	pos = isl_set_find_dim_by_id(set, isl_dim_param, var);
	if (pos >= 0) {
		set = isl_set_equate(set, isl_dim_param, pos, isl_dim_set, 0);
		set = isl_set_project_out(set, isl_dim_param, pos, 1);
	}

	isl_id_free(var);
	return set;
}

/* Return those elements in the space of "cond" that come after
 * (based on "sign") an element in "cond".
 */
static __isl_give isl_set *after(__isl_take isl_set *cond, int sign)
{
	isl_map *previous_to_this;

	if (sign > 0)
		previous_to_this = isl_map_lex_lt(isl_set_get_space(cond));
	else
		previous_to_this = isl_map_lex_gt(isl_set_get_space(cond));

	cond = isl_set_apply(cond, previous_to_this);

	return cond;
}

/* Remove those iterations of "domain" that have an earlier iteration
 * (based on "sign") where "skip" is satisfied.
 * "domain" has an extra outer loop compared to "skip".
 * The skip condition is first embedded in the same space as "domain".
 * If "apply_skip_map" is set, then "skip_map" is first applied
 * to the embedded skip condition before removing it from the domain.
 */
static __isl_give isl_set *apply_affine_break(__isl_take isl_set *domain,
	__isl_take isl_set *skip, int sign,
	int apply_skip_map, __isl_keep isl_map *skip_map)
{
	skip = embed(skip, isl_set_get_dim_id(domain, isl_dim_set, 0));
	if (apply_skip_map)
		skip = isl_set_apply(skip, isl_map_copy(skip_map));
	skip = isl_set_intersect(skip , isl_set_copy(domain));
	return isl_set_subtract(domain, after(skip, sign));
}

/* Create the infinite iteration domain
 *
 *	{ [id] : id >= 0 }
 */
static __isl_give isl_set *infinite_domain(__isl_take isl_id *id)
{
	isl_ctx *ctx = isl_id_get_ctx(id);
	isl_set *domain;

	domain = isl_set_nat_universe(isl_space_set_alloc(ctx, 0, 1));
	domain = isl_set_set_dim_id(domain, isl_dim_set, 0, id);

	return domain;
}

/* Create an identity affine expression on the space containing "domain",
 * which is assumed to be one-dimensional.
 */
static __isl_give isl_aff *identity_aff(__isl_keep isl_set *domain)
{
	isl_local_space *ls;

	ls = isl_local_space_from_space(isl_set_get_space(domain));
	return isl_aff_var_on_domain(ls, isl_dim_set, 0);
}

/* Create an affine expression that maps elements
 * of a single-dimensional array "id_test" to the previous element
 * (according to "inc"), provided this element belongs to "domain".
 * That is, create the affine expression
 *
 *	{ id[x] -> id[x - inc] : x - inc in domain }
 */
static __isl_give isl_multi_pw_aff *map_to_previous(__isl_take isl_id *id_test,
	__isl_take isl_set *domain, __isl_take isl_val *inc)
{
	isl_space *space;
	isl_local_space *ls;
	isl_aff *aff;
	isl_multi_pw_aff *prev;

	space = isl_set_get_space(domain);
	ls = isl_local_space_from_space(space);
	aff = isl_aff_var_on_domain(ls, isl_dim_set, 0);
	aff = isl_aff_add_constant_val(aff, isl_val_neg(inc));
	prev = isl_multi_pw_aff_from_pw_aff(isl_pw_aff_from_aff(aff));
	domain = isl_set_preimage_multi_pw_aff(domain,
						isl_multi_pw_aff_copy(prev));
	prev = isl_multi_pw_aff_intersect_domain(prev, domain);
	prev = isl_multi_pw_aff_set_tuple_id(prev, isl_dim_out, id_test);

	return prev;
}

/* Add an implication to "scop" expressing that if an element of
 * virtual array "id_test" has value "satisfied" then all previous elements
 * of this array also have that value.  The set of previous elements
 * is bounded by "domain".  If "sign" is negative then the iterator
 * is decreasing and we express that all subsequent array elements
 * (but still defined previously) have the same value.
 */
static struct pet_scop *add_implication(struct pet_scop *scop,
	__isl_take isl_id *id_test, __isl_take isl_set *domain, int sign,
	int satisfied)
{
	isl_space *space;
	isl_map *map;

	domain = isl_set_set_tuple_id(domain, id_test);
	space = isl_set_get_space(domain);
	if (sign > 0)
		map = isl_map_lex_ge(space);
	else
		map = isl_map_lex_le(space);
	map = isl_map_intersect_range(map, domain);
	scop = pet_scop_add_implication(scop, map, satisfied);

	return scop;
}

/* Add a filter to "scop" that imposes that it is only executed
 * when the variable identified by "id_test" has a zero value
 * for all previous iterations of "domain".
 *
 * In particular, add a filter that imposes that the array
 * has a zero value at the previous iteration of domain and
 * add an implication that implies that it then has that
 * value for all previous iterations.
 */
static struct pet_scop *scop_add_break(struct pet_scop *scop,
	__isl_take isl_id *id_test, __isl_take isl_set *domain,
	__isl_take isl_val *inc)
{
	isl_multi_pw_aff *prev;
	int sign = isl_val_sgn(inc);

	prev = map_to_previous(isl_id_copy(id_test), isl_set_copy(domain), inc);
	scop = add_implication(scop, id_test, domain, sign, 0);
	scop = pet_scop_filter(scop, prev, 0);

	return scop;
}

static struct pet_scop *scop_from_tree(__isl_keep pet_tree *tree,
	__isl_keep pet_context *pc, struct pet_state *state);

/* Construct a pet_scop for an infinite loop around the given body
 * within the context "pc".
 *
 * We extract a pet_scop for the body and then embed it in a loop with
 * iteration domain
 *
 *	{ [t] : t >= 0 }
 *
 * and schedule
 *
 *	{ [t] -> [t] }
 *
 * If the body contains any break, then it is taken into
 * account in apply_affine_break (if the skip condition is affine)
 * or in scop_add_break (if the skip condition is not affine).
 *
 * Note that in case of an affine skip condition,
 * since we are dealing with a loop without loop iterator,
 * the skip condition cannot refer to the current loop iterator and
 * so effectively, the iteration domain is of the form
 *
 *	{ [0]; [t] : t >= 1 and not skip }
 */
static struct pet_scop *scop_from_infinite_loop(__isl_keep pet_tree *body,
	__isl_keep pet_context *pc, struct pet_state *state)
{
	isl_ctx *ctx;
	isl_id *id, *id_test;
	isl_set *domain;
	isl_set *skip;
	isl_aff *ident;
	struct pet_scop *scop;
	int has_affine_break;
	int has_var_break;

	scop = scop_from_tree(body, pc, state);

	ctx = pet_tree_get_ctx(body);
	id = isl_id_alloc(ctx, "t", NULL);
	domain = infinite_domain(isl_id_copy(id));
	ident = identity_aff(domain);

	has_affine_break = pet_scop_has_affine_skip(scop, pet_skip_later);
	if (has_affine_break)
		skip = pet_scop_get_affine_skip_domain(scop, pet_skip_later);
	has_var_break = pet_scop_has_var_skip(scop, pet_skip_later);
	if (has_var_break)
		id_test = pet_scop_get_skip_id(scop, pet_skip_later);

	scop = pet_scop_embed(scop, isl_set_copy(domain),
				isl_aff_copy(ident), ident, id);
	if (has_affine_break) {
		domain = apply_affine_break(domain, skip, 1, 0, NULL);
		scop = pet_scop_intersect_domain_prefix(scop,
							isl_set_copy(domain));
	}
	if (has_var_break)
		scop = scop_add_break(scop, id_test, domain, isl_val_one(ctx));
	else
		isl_set_free(domain);

	return scop;
}

/* Construct a pet_scop for an infinite loop, i.e., a loop of the form
 *
 *	for (;;)
 *		body
 *
 * within the context "pc".
 */
static struct pet_scop *scop_from_infinite_for(__isl_keep pet_tree *tree,
	__isl_keep pet_context *pc, struct pet_state *state)
{
	struct pet_scop *scop;

	pc = pet_context_copy(pc);
	pc = pet_context_clear_writes_in_tree(pc, tree->u.l.body);

	scop = scop_from_infinite_loop(tree->u.l.body, pc, state);

	pet_context_free(pc);

	return scop;
}

/* Construct a pet_scop for a while loop of the form
 *
 *	while (pa)
 *		body
 *
 * within the context "pc".
 * In particular, construct a scop for an infinite loop around body and
 * intersect the domain with the affine expression.
 * Note that this intersection may result in an empty loop.
 */
static struct pet_scop *scop_from_affine_while(__isl_keep pet_tree *tree,
	__isl_take isl_pw_aff *pa, __isl_take pet_context *pc,
	struct pet_state *state)
{
	struct pet_scop *scop;
	isl_set *dom;
	isl_set *valid;

	valid = isl_pw_aff_domain(isl_pw_aff_copy(pa));
	dom = isl_pw_aff_non_zero_set(pa);
	scop = scop_from_infinite_loop(tree->u.l.body, pc, state);
	scop = pet_scop_restrict(scop, isl_set_params(dom));
	scop = pet_scop_restrict_context(scop, isl_set_params(valid));

	pet_context_free(pc);
	return scop;
}

/* Construct a scop for a while, given the scops for the condition
 * and the body, the filter identifier and the iteration domain of
 * the while loop.
 *
 * In particular, the scop for the condition is filtered to depend
 * on "id_test" evaluating to true for all previous iterations
 * of the loop, while the scop for the body is filtered to depend
 * on "id_test" evaluating to true for all iterations up to the
 * current iteration.
 * The actual filter only imposes that this virtual array has
 * value one on the previous or the current iteration.
 * The fact that this condition also applies to the previous
 * iterations is enforced by an implication.
 *
 * These filtered scops are then combined into a single scop.
 *
 * "sign" is positive if the iterator increases and negative
 * if it decreases.
 */
static struct pet_scop *scop_add_while(struct pet_scop *scop_cond,
	struct pet_scop *scop_body, __isl_take isl_id *id_test,
	__isl_take isl_set *domain, __isl_take isl_val *inc)
{
	isl_ctx *ctx = isl_set_get_ctx(domain);
	isl_space *space;
	isl_multi_pw_aff *test_index;
	isl_multi_pw_aff *prev;
	int sign = isl_val_sgn(inc);
	struct pet_scop *scop;

	prev = map_to_previous(isl_id_copy(id_test), isl_set_copy(domain), inc);
	scop_cond = pet_scop_filter(scop_cond, prev, 1);

	space = isl_space_map_from_set(isl_set_get_space(domain));
	test_index = isl_multi_pw_aff_identity(space);
	test_index = isl_multi_pw_aff_set_tuple_id(test_index, isl_dim_out,
						isl_id_copy(id_test));
	scop_body = pet_scop_filter(scop_body, test_index, 1);

	scop = pet_scop_add_seq(ctx, scop_cond, scop_body);
	scop = add_implication(scop, id_test, domain, sign, 1);

	return scop;
}

/* Create a pet_scop with a single statement with name S_<stmt_nr>,
 * evaluating "cond" and writing the result to a virtual scalar,
 * as expressed by "index".
 * Do so within the context "pc".
 * The location of the statement is set to "loc".
 */
static struct pet_scop *scop_from_non_affine_condition(
	__isl_take pet_expr *cond, int stmt_nr,
	__isl_take isl_multi_pw_aff *index,
	__isl_take pet_loc *loc, __isl_keep pet_context *pc)
{
	pet_expr *expr, *write;

	write = pet_expr_from_index(index);
	write = pet_expr_access_set_write(write, 1);
	write = pet_expr_access_set_read(write, 0);
	expr = pet_expr_new_binary(1, pet_op_assign, write, cond);

	return scop_from_expr(expr, NULL, stmt_nr, loc, pc);
}

/* Construct a generic while scop, with iteration domain
 * { [t] : t >= 0 } around "scop_body" within the context "pc".
 * The scop consists of two parts,
 * one for evaluating the condition "cond" and one for the body.
 * "test_nr" is the sequence number of the virtual test variable that contains
 * the result of the condition and "stmt_nr" is the sequence number
 * of the statement that evaluates the condition.
 * If "scop_inc" is not NULL, then it is added at the end of the body,
 * after replacing any skip conditions resulting from continue statements
 * by the skip conditions resulting from break statements (if any).
 *
 * The schedule is adjusted to reflect that the condition is evaluated
 * before the body is executed and the body is filtered to depend
 * on the result of the condition evaluating to true on all iterations
 * up to the current iteration, while the evaluation of the condition itself
 * is filtered to depend on the result of the condition evaluating to true
 * on all previous iterations.
 * The context of the scop representing the body is dropped
 * because we don't know how many times the body will be executed,
 * if at all.
 *
 * If the body contains any break, then it is taken into
 * account in apply_affine_break (if the skip condition is affine)
 * or in scop_add_break (if the skip condition is not affine).
 *
 * Note that in case of an affine skip condition,
 * since we are dealing with a loop without loop iterator,
 * the skip condition cannot refer to the current loop iterator and
 * so effectively, the iteration domain is of the form
 *
 *	{ [0]; [t] : t >= 1 and not skip }
 */
static struct pet_scop *scop_from_non_affine_while(__isl_take pet_expr *cond,
	int test_nr, int stmt_nr, __isl_take pet_loc *loc,
	struct pet_scop *scop_body, struct pet_scop *scop_inc,
	__isl_take pet_context *pc, struct pet_state *state)
{
	isl_ctx *ctx;
	isl_id *id, *id_test, *id_break_test;
	isl_multi_pw_aff *test_index;
	isl_set *domain;
	isl_set *skip;
	isl_aff *ident;
	struct pet_scop *scop;
	int has_affine_break;
	int has_var_break;

	ctx = state->ctx;
	test_index = pet_create_test_index(ctx, test_nr);
	scop = scop_from_non_affine_condition(cond, stmt_nr,
				isl_multi_pw_aff_copy(test_index), loc, pc);
	id_test = isl_multi_pw_aff_get_tuple_id(test_index, isl_dim_out);
	scop = pet_scop_add_boolean_array(scop, test_index, state->int_size);

	id = isl_id_alloc(ctx, "t", NULL);
	domain = infinite_domain(isl_id_copy(id));
	ident = identity_aff(domain);

	has_affine_break = pet_scop_has_affine_skip(scop_body, pet_skip_later);
	if (has_affine_break)
		skip = pet_scop_get_affine_skip_domain(scop_body,
							pet_skip_later);
	has_var_break = pet_scop_has_var_skip(scop_body, pet_skip_later);
	if (has_var_break)
		id_break_test = pet_scop_get_skip_id(scop_body, pet_skip_later);

	scop = pet_scop_prefix(scop, 0);
	scop = pet_scop_embed(scop, isl_set_copy(domain), isl_aff_copy(ident),
				isl_aff_copy(ident), isl_id_copy(id));
	scop_body = pet_scop_reset_context(scop_body);
	scop_body = pet_scop_prefix(scop_body, 1);
	if (scop_inc) {
		scop_inc = pet_scop_prefix(scop_inc, 2);
		if (pet_scop_has_skip(scop_body, pet_skip_later)) {
			isl_multi_pw_aff *skip;
			skip = pet_scop_get_skip(scop_body, pet_skip_later);
			scop_body = pet_scop_set_skip(scop_body,
							pet_skip_now, skip);
		} else
			pet_scop_reset_skip(scop_body, pet_skip_now);
		scop_body = pet_scop_add_seq(ctx, scop_body, scop_inc);
	}
	scop_body = pet_scop_embed(scop_body, isl_set_copy(domain),
				    isl_aff_copy(ident), ident, id);

	if (has_affine_break) {
		domain = apply_affine_break(domain, skip, 1, 0, NULL);
		scop = pet_scop_intersect_domain_prefix(scop,
							isl_set_copy(domain));
		scop_body = pet_scop_intersect_domain_prefix(scop_body,
							isl_set_copy(domain));
	}
	if (has_var_break) {
		scop = scop_add_break(scop, isl_id_copy(id_break_test),
					isl_set_copy(domain), isl_val_one(ctx));
		scop_body = scop_add_break(scop_body, id_break_test,
					isl_set_copy(domain), isl_val_one(ctx));
	}
	scop = scop_add_while(scop, scop_body, id_test, domain,
				isl_val_one(ctx));

	pet_context_free(pc);
	return scop;
}

/* Check if the while loop is of the form
 *
 *	while (affine expression)
 *		body
 *
 * If so, call scop_from_affine_while to construct a scop.
 *
 * Otherwise, extract the body and pass control to scop_from_non_affine_while
 * to extend the iteration domain with an infinite loop.
 *
 * "pc" is the context in which the affine expressions in the scop are created.
 */
static struct pet_scop *scop_from_while(__isl_keep pet_tree *tree,
	__isl_keep pet_context *pc, struct pet_state *state)
{
	pet_expr *cond_expr;
	int test_nr, stmt_nr;
	isl_pw_aff *pa;
	struct pet_scop *scop_body;

	if (!tree)
		return NULL;

	pc = pet_context_copy(pc);
	pc = pet_context_clear_writes_in_tree(pc, tree->u.l.body);

	cond_expr = pet_expr_copy(tree->u.l.cond);
	cond_expr = pet_expr_plug_in_args(cond_expr, pc);
	pa = pet_expr_extract_affine_condition(cond_expr, pc);
	pet_expr_free(cond_expr);

	if (!pa)
		goto error;

	if (!isl_pw_aff_involves_nan(pa))
		return scop_from_affine_while(tree, pa, pc, state);
	isl_pw_aff_free(pa);
	test_nr = state->n_test++;
	stmt_nr = state->n_stmt++;
	scop_body = scop_from_tree(tree->u.l.body, pc, state);
	return scop_from_non_affine_while(pet_expr_copy(tree->u.l.cond),
				test_nr, stmt_nr, pet_tree_get_loc(tree),
				scop_body, NULL, pc, state);
error:
	pet_context_free(pc);
	return NULL;
}

/* Check whether "cond" expresses a simple loop bound
 * on the only set dimension.
 * In particular, if "up" is set then "cond" should contain only
 * upper bounds on the set dimension.
 * Otherwise, it should contain only lower bounds.
 */
static int is_simple_bound(__isl_keep isl_set *cond, __isl_keep isl_val *inc)
{
	if (isl_val_is_pos(inc))
		return !isl_set_dim_has_any_lower_bound(cond, isl_dim_set, 0);
	else
		return !isl_set_dim_has_any_upper_bound(cond, isl_dim_set, 0);
}

/* Extend a condition on a given iteration of a loop to one that
 * imposes the same condition on all previous iterations.
 * "domain" expresses the lower [upper] bound on the iterations
 * when inc is positive [negative].
 *
 * In particular, we construct the condition (when inc is positive)
 *
 *	forall i' : (domain(i') and i' <= i) => cond(i')
 *
 * which is equivalent to
 *
 *	not exists i' : domain(i') and i' <= i and not cond(i')
 *
 * We construct this set by negating cond, applying a map
 *
 *	{ [i'] -> [i] : domain(i') and i' <= i }
 *
 * and then negating the result again.
 */
static __isl_give isl_set *valid_for_each_iteration(__isl_take isl_set *cond,
	__isl_take isl_set *domain, __isl_take isl_val *inc)
{
	isl_map *previous_to_this;

	if (isl_val_is_pos(inc))
		previous_to_this = isl_map_lex_le(isl_set_get_space(domain));
	else
		previous_to_this = isl_map_lex_ge(isl_set_get_space(domain));

	previous_to_this = isl_map_intersect_domain(previous_to_this, domain);

	cond = isl_set_complement(cond);
	cond = isl_set_apply(cond, previous_to_this);
	cond = isl_set_complement(cond);

	isl_val_free(inc);

	return cond;
}

/* Construct a domain of the form
 *
 * [id] -> { : exists a: id = init + a * inc and a >= 0 }
 */
static __isl_give isl_set *strided_domain(__isl_take isl_id *id,
	__isl_take isl_pw_aff *init, __isl_take isl_val *inc)
{
	isl_aff *aff;
	isl_space *dim;
	isl_set *set;

	init = isl_pw_aff_insert_dims(init, isl_dim_in, 0, 1);
	dim = isl_pw_aff_get_domain_space(init);
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient_val(aff, isl_dim_in, 0, inc);
	init = isl_pw_aff_add(init, isl_pw_aff_from_aff(aff));

	dim = isl_space_set_alloc(isl_pw_aff_get_ctx(init), 1, 1);
	dim = isl_space_set_dim_id(dim, isl_dim_param, 0, id);
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient_si(aff, isl_dim_param, 0, 1);

	set = isl_pw_aff_eq_set(isl_pw_aff_from_aff(aff), init);

	set = isl_set_lower_bound_si(set, isl_dim_set, 0, 0);

	return isl_set_params(set);
}

/* Assuming "cond" represents a bound on a loop where the loop
 * iterator "iv" is incremented (or decremented) by one, check if wrapping
 * is possible.
 *
 * Under the given assumptions, wrapping is only possible if "cond" allows
 * for the last value before wrapping, i.e., 2^width - 1 in case of an
 * increasing iterator and 0 in case of a decreasing iterator.
 */
static int can_wrap(__isl_keep isl_set *cond, __isl_keep pet_expr *iv,
	__isl_keep isl_val *inc)
{
	int cw;
	isl_ctx *ctx;
	isl_val *limit;
	isl_set *test;

	test = isl_set_copy(cond);

	ctx = isl_set_get_ctx(test);
	if (isl_val_is_neg(inc))
		limit = isl_val_zero(ctx);
	else {
		limit = isl_val_int_from_ui(ctx, pet_expr_get_type_size(iv));
		limit = isl_val_2exp(limit);
		limit = isl_val_sub_ui(limit, 1);
	}

	test = isl_set_fix_val(cond, isl_dim_set, 0, limit);
	cw = !isl_set_is_empty(test);
	isl_set_free(test);

	return cw;
}

/* Given a one-dimensional space, construct the following affine expression
 * on this space
 *
 *	{ [v] -> [v mod 2^width] }
 *
 * where width is the number of bits used to represent the values
 * of the unsigned variable "iv".
 */
static __isl_give isl_aff *compute_wrapping(__isl_take isl_space *dim,
	__isl_keep pet_expr *iv)
{
	isl_ctx *ctx;
	isl_val *mod;
	isl_aff *aff;

	ctx = isl_space_get_ctx(dim);
	mod = isl_val_int_from_ui(ctx, pet_expr_get_type_size(iv));
	mod = isl_val_2exp(mod);

	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient_si(aff, isl_dim_in, 0, 1);
	aff = isl_aff_mod_val(aff, mod);

	return aff;
}

/* Project out the parameter "id" from "set".
 */
static __isl_give isl_set *set_project_out_by_id(__isl_take isl_set *set,
	__isl_keep isl_id *id)
{
	int pos;

	pos = isl_set_find_dim_by_id(set, isl_dim_param, id);
	if (pos >= 0)
		set = isl_set_project_out(set, isl_dim_param, pos, 1);

	return set;
}

/* Compute the set of parameters for which "set1" is a subset of "set2".
 *
 * set1 is a subset of set2 if
 *
 *	forall i in set1 : i in set2
 *
 * or
 *
 *	not exists i in set1 and i not in set2
 *
 * i.e.,
 *
 *	not exists i in set1 \ set2
 */
static __isl_give isl_set *enforce_subset(__isl_take isl_set *set1,
	__isl_take isl_set *set2)
{
	return isl_set_complement(isl_set_params(isl_set_subtract(set1, set2)));
}

/* Compute the set of parameter values for which "cond" holds
 * on the next iteration for each element of "dom".
 *
 * We first construct mapping { [i] -> [i + inc] }, apply that to "dom"
 * and then compute the set of parameters for which the result is a subset
 * of "cond".
 */
static __isl_give isl_set *valid_on_next(__isl_take isl_set *cond,
	__isl_take isl_set *dom, __isl_take isl_val *inc)
{
	isl_space *space;
	isl_aff *aff;
	isl_map *next;

	space = isl_set_get_space(dom);
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(space));
	aff = isl_aff_add_coefficient_si(aff, isl_dim_in, 0, 1);
	aff = isl_aff_add_constant_val(aff, inc);
	next = isl_map_from_basic_map(isl_basic_map_from_aff(aff));

	dom = isl_set_apply(dom, next);

	return enforce_subset(dom, cond);
}

/* Extract the for loop "tree" as a while loop within the context "pc".
 *
 * That is, the for loop has the form
 *
 *	for (iv = init; cond; iv += inc)
 *		body;
 *
 * and is treated as
 *
 *	iv = init;
 *	while (cond) {
 *		body;
 *		iv += inc;
 *	}
 *
 * except that the skips resulting from any continue statements
 * in body do not apply to the increment, but are replaced by the skips
 * resulting from break statements.
 *
 * If the loop iterator is declared in the for loop, then it is killed before
 * and after the loop.
 */
static struct pet_scop *scop_from_non_affine_for(__isl_keep pet_tree *tree,
	__isl_take pet_context *pc, struct pet_state *state)
{
	int declared;
	int test_nr, stmt_nr;
	isl_id *iv;
	pet_expr *expr_iv, *init, *inc;
	struct pet_scop *scop_init, *scop_inc, *scop, *scop_body;
	int type_size;
	struct pet_array *array;
	struct pet_scop *scop_kill;

	iv = pet_expr_access_get_id(tree->u.l.iv);
	pc = pet_context_mark_assigned(pc, iv);

	declared = tree->u.l.declared;

	expr_iv = pet_expr_copy(tree->u.l.iv);
	type_size = pet_expr_get_type_size(expr_iv);
	init = pet_expr_copy(tree->u.l.init);
	init = pet_expr_new_binary(type_size, pet_op_assign, expr_iv, init);
	scop_init = scop_from_expr(init, NULL, state->n_stmt++,
					pet_tree_get_loc(tree), pc);
	scop_init = pet_scop_prefix(scop_init, declared);

	test_nr = state->n_test++;
	stmt_nr = state->n_stmt++;
	scop_body = scop_from_tree(tree->u.l.body, pc, state);

	expr_iv = pet_expr_copy(tree->u.l.iv);
	type_size = pet_expr_get_type_size(expr_iv);
	inc = pet_expr_copy(tree->u.l.inc);
	inc = pet_expr_new_binary(type_size, pet_op_add_assign, expr_iv, inc);
	scop_inc = scop_from_expr(inc, NULL, state->n_stmt++,
				pet_tree_get_loc(tree), pc);

	scop = scop_from_non_affine_while(pet_expr_copy(tree->u.l.cond),
			test_nr, stmt_nr, pet_tree_get_loc(tree),
			scop_body, scop_inc, pet_context_copy(pc), state);

	scop = pet_scop_prefix(scop, declared + 1);
	scop = pet_scop_add_seq(state->ctx, scop_init, scop);

	if (!declared) {
		pet_context_free(pc);
		return scop;
	}

	array = extract_array(tree->u.l.iv, pc, state);
	if (array)
		array->declared = 1;
	scop_kill = kill(pet_tree_get_loc(tree), array, pc, state);
	scop_kill = pet_scop_prefix(scop_kill, 0);
	scop = pet_scop_add_seq(state->ctx, scop_kill, scop);
	scop_kill = kill(pet_tree_get_loc(tree), array, pc, state);
	scop_kill = pet_scop_add_array(scop_kill, array);
	scop_kill = pet_scop_prefix(scop_kill, 3);
	scop = pet_scop_add_seq(state->ctx, scop, scop_kill);

	pet_context_free(pc);
	return scop;
}

/* Given an access expression "expr", is the variable accessed by
 * "expr" assigned anywhere inside "tree"?
 */
static int is_assigned(__isl_keep pet_expr *expr, __isl_keep pet_tree *tree)
{
	int assigned = 0;
	isl_id *id;

	id = pet_expr_access_get_id(expr);
	assigned = pet_tree_writes(tree, id);
	isl_id_free(id);

	return assigned;
}

/* Are all nested access parameters in "pa" allowed given "tree".
 * In particular, is none of them written by anywhere inside "tree".
 *
 * If "tree" has any continue nodes in the current loop level,
 * then no nested access parameters are allowed.
 * In particular, if there is any nested access in a guard
 * for a piece of code containing a "continue", then we want to introduce
 * a separate statement for evaluating this guard so that we can express
 * that the result is false for all previous iterations.
 */
static int is_nested_allowed(__isl_keep isl_pw_aff *pa,
	__isl_keep pet_tree *tree)
{
	int i, nparam;

	if (!tree)
		return -1;

	if (!pet_nested_any_in_pw_aff(pa))
		return 1;

	if (pet_tree_has_continue(tree))
		return 0;

	nparam = isl_pw_aff_dim(pa, isl_dim_param);
	for (i = 0; i < nparam; ++i) {
		isl_id *id = isl_pw_aff_get_dim_id(pa, isl_dim_param, i);
		pet_expr *expr;
		int allowed;

		if (!pet_nested_in_id(id)) {
			isl_id_free(id);
			continue;
		}

		expr = pet_nested_extract_expr(id);
		allowed = pet_expr_get_type(expr) == pet_expr_access &&
			    !is_assigned(expr, tree);

		pet_expr_free(expr);
		isl_id_free(id);

		if (!allowed)
			return 0;
	}

	return 1;
}

/* Construct a pet_scop for a for tree with static affine initialization
 * and constant increment within the context "pc".
 *
 * The condition is allowed to contain nested accesses, provided
 * they are not being written to inside the body of the loop.
 * Otherwise, or if the condition is otherwise non-affine, the for loop is
 * essentially treated as a while loop, with iteration domain
 * { [i] : i >= init }.
 *
 * We extract a pet_scop for the body and then embed it in a loop with
 * iteration domain and schedule
 *
 *	{ [i] : i >= init and condition' }
 *	{ [i] -> [i] }
 *
 * or
 *
 *	{ [i] : i <= init and condition' }
 *	{ [i] -> [-i] }
 *
 * Where condition' is equal to condition if the latter is
 * a simple upper [lower] bound and a condition that is extended
 * to apply to all previous iterations otherwise.
 *
 * If the condition is non-affine, then we drop the condition from the
 * iteration domain and instead create a separate statement
 * for evaluating the condition.  The body is then filtered to depend
 * on the result of the condition evaluating to true on all iterations
 * up to the current iteration, while the evaluation the condition itself
 * is filtered to depend on the result of the condition evaluating to true
 * on all previous iterations.
 * The context of the scop representing the body is dropped
 * because we don't know how many times the body will be executed,
 * if at all.
 *
 * If the stride of the loop is not 1, then "i >= init" is replaced by
 *
 *	(exists a: i = init + stride * a and a >= 0)
 *
 * If the loop iterator i is unsigned, then wrapping may occur.
 * We therefore use a virtual iterator instead that does not wrap.
 * However, the condition in the code applies
 * to the wrapped value, so we need to change condition(i)
 * into condition([i % 2^width]).  Similarly, we replace all accesses
 * to the original iterator by the wrapping of the virtual iterator.
 * Note that there may be no need to perform this final wrapping
 * if the loop condition (after wrapping) satisfies certain conditions.
 * However, the is_simple_bound condition is not enough since it doesn't
 * check if there even is an upper bound.
 *
 * Wrapping on unsigned iterators can be avoided entirely if
 * loop condition is simple, the loop iterator is incremented
 * [decremented] by one and the last value before wrapping cannot
 * possibly satisfy the loop condition.
 *
 * Valid parameters for a for loop are those for which the initial
 * value itself, the increment on each domain iteration and
 * the condition on both the initial value and
 * the result of incrementing the iterator for each iteration of the domain
 * can be evaluated.
 * If the loop condition is non-affine, then we only consider validity
 * of the initial value.
 *
 * If the body contains any break, then we keep track of it in "skip"
 * (if the skip condition is affine) or it is handled in scop_add_break
 * (if the skip condition is not affine).
 * Note that the affine break condition needs to be considered with
 * respect to previous iterations in the virtual domain (if any).
 */
static struct pet_scop *scop_from_affine_for(__isl_keep pet_tree *tree,
	__isl_take isl_pw_aff *init_val, __isl_take isl_pw_aff *pa_inc,
	__isl_take isl_val *inc, __isl_take pet_context *pc,
	struct pet_state *state)
{
	isl_local_space *ls;
	isl_set *domain;
	isl_aff *sched;
	isl_set *cond = NULL;
	isl_set *skip = NULL;
	isl_id *id, *id_test = NULL, *id_break_test;
	struct pet_scop *scop, *scop_cond = NULL;
	int is_one;
	int is_unsigned;
	int is_simple;
	int is_virtual;
	int is_non_affine;
	int has_affine_break;
	int has_var_break;
	isl_map *rev_wrap = NULL;
	isl_aff *wrap = NULL;
	isl_pw_aff *pa;
	isl_set *valid_init;
	isl_set *valid_cond;
	isl_set *valid_cond_init;
	isl_set *valid_cond_next;
	isl_set *valid_inc;
	pet_expr *cond_expr;
	pet_context *pc_nested;

	id = pet_expr_access_get_id(tree->u.l.iv);

	cond_expr = pet_expr_copy(tree->u.l.cond);
	cond_expr = pet_expr_plug_in_args(cond_expr, pc);
	pc_nested = pet_context_copy(pc);
	pc_nested = pet_context_set_allow_nested(pc_nested, 1);
	pa = pet_expr_extract_affine_condition(cond_expr, pc_nested);
	pet_context_free(pc_nested);
	pet_expr_free(cond_expr);

	valid_inc = isl_pw_aff_domain(pa_inc);

	is_unsigned = pet_expr_get_type_size(tree->u.l.iv) > 0;

	is_non_affine = isl_pw_aff_involves_nan(pa) ||
			!is_nested_allowed(pa, tree->u.l.body);
	if (is_non_affine)
		pa = isl_pw_aff_free(pa);

	valid_cond = isl_pw_aff_domain(isl_pw_aff_copy(pa));
	cond = isl_pw_aff_non_zero_set(pa);
	if (is_non_affine) {
		isl_multi_pw_aff *test_index;
		test_index = pet_create_test_index(state->ctx, state->n_test++);
		scop_cond = scop_from_non_affine_condition(
				pet_expr_copy(tree->u.l.cond), state->n_stmt++,
				isl_multi_pw_aff_copy(test_index),
				pet_tree_get_loc(tree), pc);
		id_test = isl_multi_pw_aff_get_tuple_id(test_index,
							isl_dim_out);
		scop_cond = pet_scop_add_boolean_array(scop_cond, test_index,
				state->int_size);
		scop_cond = pet_scop_prefix(scop_cond, 0);
		cond = isl_set_universe(isl_space_set_alloc(state->ctx, 0, 0));
	}

	cond = embed(cond, isl_id_copy(id));
	valid_cond = isl_set_coalesce(valid_cond);
	valid_cond = embed(valid_cond, isl_id_copy(id));
	valid_inc = embed(valid_inc, isl_id_copy(id));
	is_one = isl_val_is_one(inc) || isl_val_is_negone(inc);
	is_virtual = is_unsigned &&
		(!is_one || can_wrap(cond, tree->u.l.iv, inc));

	valid_cond_init = enforce_subset(
		isl_map_range(isl_map_from_pw_aff(isl_pw_aff_copy(init_val))),
		isl_set_copy(valid_cond));
	if (is_one && !is_virtual) {
		isl_pw_aff_free(init_val);
		pa = pet_expr_extract_comparison(
			isl_val_is_pos(inc) ? pet_op_ge : pet_op_le,
				tree->u.l.iv, tree->u.l.init, pc);
		valid_init = isl_pw_aff_domain(isl_pw_aff_copy(pa));
		valid_init = set_project_out_by_id(valid_init, id);
		domain = isl_pw_aff_non_zero_set(pa);
	} else {
		valid_init = isl_pw_aff_domain(isl_pw_aff_copy(init_val));
		domain = strided_domain(isl_id_copy(id), init_val,
					isl_val_copy(inc));
	}

	domain = embed(domain, isl_id_copy(id));
	if (is_virtual) {
		wrap = compute_wrapping(isl_set_get_space(cond), tree->u.l.iv);
		rev_wrap = isl_map_from_aff(isl_aff_copy(wrap));
		rev_wrap = isl_map_reverse(rev_wrap);
		cond = isl_set_apply(cond, isl_map_copy(rev_wrap));
		valid_cond = isl_set_apply(valid_cond, isl_map_copy(rev_wrap));
		valid_inc = isl_set_apply(valid_inc, isl_map_copy(rev_wrap));
	}
	is_simple = is_simple_bound(cond, inc);
	if (!is_simple) {
		cond = isl_set_gist(cond, isl_set_copy(domain));
		is_simple = is_simple_bound(cond, inc);
	}
	if (!is_simple)
		cond = valid_for_each_iteration(cond,
				    isl_set_copy(domain), isl_val_copy(inc));
	domain = isl_set_intersect(domain, cond);
	domain = isl_set_set_dim_id(domain, isl_dim_set, 0, isl_id_copy(id));
	ls = isl_local_space_from_space(isl_set_get_space(domain));
	sched = isl_aff_var_on_domain(ls, isl_dim_set, 0);
	if (isl_val_is_neg(inc))
		sched = isl_aff_neg(sched);

	valid_cond_next = valid_on_next(valid_cond, isl_set_copy(domain),
					isl_val_copy(inc));
	valid_inc = enforce_subset(isl_set_copy(domain), valid_inc);

	if (!is_virtual)
		wrap = identity_aff(domain);

	scop = scop_from_tree(tree->u.l.body, pc, state);

	scop_cond = pet_scop_embed(scop_cond, isl_set_copy(domain),
		    isl_aff_copy(sched), isl_aff_copy(wrap), isl_id_copy(id));
	has_affine_break = scop &&
				pet_scop_has_affine_skip(scop, pet_skip_later);
	if (has_affine_break)
		skip = pet_scop_get_affine_skip_domain(scop, pet_skip_later);
	has_var_break = scop && pet_scop_has_var_skip(scop, pet_skip_later);
	if (has_var_break)
		id_break_test = pet_scop_get_skip_id(scop, pet_skip_later);
	if (is_non_affine) {
		scop = pet_scop_reset_context(scop);
		scop = pet_scop_prefix(scop, 1);
	}
	scop = pet_scop_embed(scop, isl_set_copy(domain), sched, wrap, id);
	scop = pet_scop_resolve_nested(scop);
	if (has_affine_break) {
		domain = apply_affine_break(domain, skip, isl_val_sgn(inc),
					    is_virtual, rev_wrap);
		scop = pet_scop_intersect_domain_prefix(scop,
							isl_set_copy(domain));
	}
	isl_map_free(rev_wrap);
	if (has_var_break)
		scop = scop_add_break(scop, id_break_test, isl_set_copy(domain),
					isl_val_copy(inc));
	if (is_non_affine) {
		scop = scop_add_while(scop_cond, scop, id_test, domain,
					isl_val_copy(inc));
		isl_set_free(valid_inc);
	} else {
		scop = pet_scop_restrict_context(scop, valid_inc);
		scop = pet_scop_restrict_context(scop, valid_cond_next);
		scop = pet_scop_restrict_context(scop, valid_cond_init);
		isl_set_free(domain);
	}

	isl_val_free(inc);

	scop = pet_scop_restrict_context(scop, isl_set_params(valid_init));

	pet_context_free(pc);
	return scop;
}

/* Construct a pet_scop for a for statement within the context of "pc".
 *
 * We update the context to reflect the writes to the loop variable and
 * the writes inside the body.
 *
 * Then we check if the initialization of the for loop
 * is a static affine value and the increment is a constant.
 * If so, we construct the pet_scop using scop_from_affine_for.
 * Otherwise, we treat the for loop as a while loop
 * in scop_from_non_affine_for.
 */
static struct pet_scop *scop_from_for(__isl_keep pet_tree *tree,
	__isl_keep pet_context *pc, struct pet_state *state)
{
	isl_id *iv;
	isl_val *inc;
	isl_pw_aff *pa_inc, *init_val;
	pet_context *pc_init_val;

	if (!tree)
		return NULL;

	iv = pet_expr_access_get_id(tree->u.l.iv);
	pc = pet_context_copy(pc);
	pc = pet_context_clear_value(pc, iv);
	pc = pet_context_clear_writes_in_tree(pc, tree->u.l.body);

	pc_init_val = pet_context_copy(pc);
	pc_init_val = pet_context_mark_unknown(pc_init_val, isl_id_copy(iv));
	init_val = pet_expr_extract_affine(tree->u.l.init, pc_init_val);
	pet_context_free(pc_init_val);
	pa_inc = pet_expr_extract_affine(tree->u.l.inc, pc);
	inc = pet_extract_cst(pa_inc);
	if (!pa_inc || !init_val || !inc)
		goto error;
	if (!isl_pw_aff_involves_nan(pa_inc) &&
	    !isl_pw_aff_involves_nan(init_val) && !isl_val_is_nan(inc))
		return scop_from_affine_for(tree, init_val, pa_inc, inc,
						pc, state);

	isl_pw_aff_free(pa_inc);
	isl_pw_aff_free(init_val);
	isl_val_free(inc);
	return scop_from_non_affine_for(tree, pc, state);
error:
	isl_pw_aff_free(pa_inc);
	isl_pw_aff_free(init_val);
	isl_val_free(inc);
	pet_context_free(pc);
	return NULL;
}

/* Check whether "expr" is an affine constraint within the context "pc".
 */
static int is_affine_condition(__isl_keep pet_expr *expr,
	__isl_keep pet_context *pc)
{
	isl_pw_aff *pa;
	int is_affine;

	pa = pet_expr_extract_affine_condition(expr, pc);
	if (!pa)
		return -1;
	is_affine = !isl_pw_aff_involves_nan(pa);
	isl_pw_aff_free(pa);

	return is_affine;
}

/* Check if the given if statement is a conditional assignement
 * with a non-affine condition.
 *
 * In particular we check if "stmt" is of the form
 *
 *	if (condition)
 *		a = f(...);
 *	else
 *		a = g(...);
 *
 * where the condition is non-affine and a is some array or scalar access.
 */
static int is_conditional_assignment(__isl_keep pet_tree *tree,
	__isl_keep pet_context *pc)
{
	int equal;
	isl_ctx *ctx;
	pet_expr *expr1, *expr2;

	ctx = pet_tree_get_ctx(tree);
	if (!pet_options_get_detect_conditional_assignment(ctx))
		return 0;
	if (tree->type != pet_tree_if_else)
		return 0;
	if (tree->u.i.then_body->type != pet_tree_expr)
		return 0;
	if (tree->u.i.else_body->type != pet_tree_expr)
		return 0;
	expr1 = tree->u.i.then_body->u.e.expr;
	expr2 = tree->u.i.else_body->u.e.expr;
	if (pet_expr_get_type(expr1) != pet_expr_op)
		return 0;
	if (pet_expr_get_type(expr2) != pet_expr_op)
		return 0;
	if (pet_expr_op_get_type(expr1) != pet_op_assign)
		return 0;
	if (pet_expr_op_get_type(expr2) != pet_op_assign)
		return 0;
	expr1 = pet_expr_get_arg(expr1, 0);
	expr2 = pet_expr_get_arg(expr2, 0);
	equal = pet_expr_is_equal(expr1, expr2);
	pet_expr_free(expr1);
	pet_expr_free(expr2);
	if (equal < 0 || !equal)
		return 0;
	if (is_affine_condition(tree->u.i.cond, pc))
		return 0;

	return 1;
}

/* Given that "tree" is of the form
 *
 *	if (condition)
 *		a = f(...);
 *	else
 *		a = g(...);
 *
 * where a is some array or scalar access, construct a pet_scop
 * corresponding to this conditional assignment within the context "pc".
 *
 * The constructed pet_scop then corresponds to the expression
 *
 *	a = condition ? f(...) : g(...)
 *
 * All access relations in f(...) are intersected with condition
 * while all access relation in g(...) are intersected with the complement.
 */
static struct pet_scop *scop_from_conditional_assignment(
	__isl_keep pet_tree *tree, __isl_take pet_context *pc,
	struct pet_state *state)
{
	int type_size;
	isl_pw_aff *pa;
	isl_set *cond, *comp;
	isl_multi_pw_aff *index;
	pet_expr *expr1, *expr2;
	pet_expr *pe_cond, *pe_then, *pe_else, *pe, *pe_write;
	pet_context *pc_nested;
	struct pet_scop *scop;

	pe_cond = pet_expr_copy(tree->u.i.cond);
	pe_cond = pet_expr_plug_in_args(pe_cond, pc);
	pc_nested = pet_context_copy(pc);
	pc_nested = pet_context_set_allow_nested(pc_nested, 1);
	pa = pet_expr_extract_affine_condition(pe_cond, pc_nested);
	pet_context_free(pc_nested);
	pet_expr_free(pe_cond);
	cond = isl_pw_aff_non_zero_set(isl_pw_aff_copy(pa));
	comp = isl_pw_aff_zero_set(isl_pw_aff_copy(pa));
	index = isl_multi_pw_aff_from_pw_aff(pa);

	expr1 = tree->u.i.then_body->u.e.expr;
	expr2 = tree->u.i.else_body->u.e.expr;

	pe_cond = pet_expr_from_index(index);

	pe_then = pet_expr_get_arg(expr1, 1);
	pe_then = pet_expr_restrict(pe_then, cond);
	pe_else = pet_expr_get_arg(expr2, 1);
	pe_else = pet_expr_restrict(pe_else, comp);
	pe_write = pet_expr_get_arg(expr1, 0);

	pe = pet_expr_new_ternary(pe_cond, pe_then, pe_else);
	type_size = pet_expr_get_type_size(pe_write);
	pe = pet_expr_new_binary(type_size, pet_op_assign, pe_write, pe);

	scop = scop_from_expr(pe, NULL, state->n_stmt++,
				pet_tree_get_loc(tree), pc);

	pet_context_free(pc);

	return scop;
}

/* Construct a pet_scop for a non-affine if statement within the context "pc".
 *
 * We create a separate statement that writes the result
 * of the non-affine condition to a virtual scalar.
 * A constraint requiring the value of this virtual scalar to be one
 * is added to the iteration domains of the then branch.
 * Similarly, a constraint requiring the value of this virtual scalar
 * to be zero is added to the iteration domains of the else branch, if any.
 * We adjust the schedules to ensure that the virtual scalar is written
 * before it is read.
 *
 * If there are any breaks or continues in the then and/or else
 * branches, then we may have to compute a new skip condition.
 * This is handled using a pet_skip_info object.
 * On initialization, the object checks if skip conditions need
 * to be computed.  If so, it does so in pet_skip_info_if_extract_index and
 * adds them in pet_skip_info_if_add.
 */
static struct pet_scop *scop_from_non_affine_if(__isl_keep pet_tree *tree,
	struct pet_scop *scop_then, struct pet_scop *scop_else, int stmt_id,
	__isl_take pet_context *pc, struct pet_state *state)
{
	int has_else;
	int save_n_stmt = state->n_stmt;
	isl_multi_pw_aff *test_index;
	struct pet_skip_info skip;
	struct pet_scop *scop;

	has_else = tree->type == pet_tree_if_else;

	test_index = pet_create_test_index(state->ctx, state->n_test++);
	state->n_stmt = stmt_id;
	scop = scop_from_non_affine_condition(pet_expr_copy(tree->u.i.cond),
		state->n_stmt++, isl_multi_pw_aff_copy(test_index),
		pet_tree_get_loc(tree), pc);
	state->n_stmt = save_n_stmt;
	scop = pet_scop_add_boolean_array(scop,
		isl_multi_pw_aff_copy(test_index), state->int_size);

	pet_skip_info_if_init(&skip, state->ctx, scop_then, scop_else,
					has_else, 0);
	pet_skip_info_if_extract_index(&skip, test_index, state);

	scop = pet_scop_prefix(scop, 0);
	scop_then = pet_scop_prefix(scop_then, 1);
	scop_then = pet_scop_filter(scop_then,
					isl_multi_pw_aff_copy(test_index), 1);
	if (has_else) {
		scop_else = pet_scop_prefix(scop_else, 1);
		scop_else = pet_scop_filter(scop_else, test_index, 0);
		scop_then = pet_scop_add_par(state->ctx, scop_then, scop_else);
	} else
		isl_multi_pw_aff_free(test_index);

	scop = pet_scop_add_seq(state->ctx, scop, scop_then);

	scop = pet_skip_info_if_add(&skip, scop, 2);

	pet_context_free(pc);
	return scop;
}

/* Construct a pet_scop for an affine if statement within the context "pc".
 *
 * The condition is added to the iteration domains of the then branch,
 * while the opposite of the condition in added to the iteration domains
 * of the else branch, if any.
 *
 * If there are any breaks or continues in the then and/or else
 * branches, then we may have to compute a new skip condition.
 * This is handled using a pet_skip_info_if object.
 * On initialization, the object checks if skip conditions need
 * to be computed.  If so, it does so in pet_skip_info_if_extract_cond and
 * adds them in pet_skip_info_if_add.
 */
static struct pet_scop *scop_from_affine_if(__isl_keep pet_tree *tree,
	__isl_take isl_pw_aff *cond,
	struct pet_scop *scop_then, struct pet_scop *scop_else,
	struct pet_state *state)
{
	int has_else;
	isl_ctx *ctx;
	isl_set *set;
	isl_set *valid;
	struct pet_skip_info skip;
	struct pet_scop *scop;

	ctx = pet_tree_get_ctx(tree);

	has_else = tree->type == pet_tree_if_else;

	pet_skip_info_if_init(&skip, ctx, scop_then, scop_else, has_else, 1);
	pet_skip_info_if_extract_cond(&skip, cond, state);

	valid = isl_pw_aff_domain(isl_pw_aff_copy(cond));
	set = isl_pw_aff_non_zero_set(cond);
	scop = pet_scop_restrict(scop_then, isl_set_params(isl_set_copy(set)));

	if (has_else) {
		set = isl_set_subtract(isl_set_copy(valid), set);
		scop_else = pet_scop_restrict(scop_else, isl_set_params(set));
		scop = pet_scop_add_par(ctx, scop, scop_else);
	} else
		isl_set_free(set);
	scop = pet_scop_resolve_nested(scop);
	scop = pet_scop_restrict_context(scop, isl_set_params(valid));

	if (pet_skip_info_has_skip(&skip))
		scop = pet_scop_prefix(scop, 0);
	scop = pet_skip_info_if_add(&skip, scop, 1);

	return scop;
}

/* Construct a pet_scop for an if statement within the context "pc".
 *
 * If the condition fits the pattern of a conditional assignment,
 * then it is handled by scop_from_conditional_assignment.
 *
 * Otherwise, we check if the condition is affine.
 * If so, we construct the scop in scop_from_affine_if.
 * Otherwise, we construct the scop in scop_from_non_affine_if.
 *
 * We allow the condition to be dynamic, i.e., to refer to
 * scalars or array elements that may be written to outside
 * of the given if statement.  These nested accesses are then represented
 * as output dimensions in the wrapping iteration domain.
 * If it is also written _inside_ the then or else branch, then
 * we treat the condition as non-affine.
 * As explained in extract_non_affine_if, this will introduce
 * an extra statement.
 * For aesthetic reasons, we want this statement to have a statement
 * number that is lower than those of the then and else branches.
 * In order to evaluate if we will need such a statement, however, we
 * first construct scops for the then and else branches.
 * We therefore reserve a statement number if we might have to
 * introduce such an extra statement.
 */
static struct pet_scop *scop_from_if(__isl_keep pet_tree *tree,
	__isl_keep pet_context *pc, struct pet_state *state)
{
	int has_else;
	int stmt_id;
	isl_pw_aff *cond;
	pet_expr *cond_expr;
	struct pet_scop *scop_then, *scop_else = NULL;
	pet_context *pc_nested;

	if (!tree)
		return NULL;

	has_else = tree->type == pet_tree_if_else;

	pc = pet_context_copy(pc);
	pc = pet_context_clear_writes_in_tree(pc, tree->u.i.then_body);
	if (has_else)
		pc = pet_context_clear_writes_in_tree(pc, tree->u.i.else_body);

	if (is_conditional_assignment(tree, pc))
		return scop_from_conditional_assignment(tree, pc, state);

	cond_expr = pet_expr_copy(tree->u.i.cond);
	cond_expr = pet_expr_plug_in_args(cond_expr, pc);
	pc_nested = pet_context_copy(pc);
	pc_nested = pet_context_set_allow_nested(pc_nested, 1);
	cond = pet_expr_extract_affine_condition(cond_expr, pc_nested);
	pet_context_free(pc_nested);
	pet_expr_free(cond_expr);

	if (!cond) {
		pet_context_free(pc);
		return NULL;
	}

	if (isl_pw_aff_involves_nan(cond) || pet_nested_any_in_pw_aff(cond))
		stmt_id = state->n_stmt++;

	scop_then = scop_from_tree(tree->u.i.then_body, pc, state);
	if (has_else)
		scop_else = scop_from_tree(tree->u.i.else_body, pc, state);

	if (isl_pw_aff_involves_nan(cond)) {
		isl_pw_aff_free(cond);
		return scop_from_non_affine_if(tree, scop_then, scop_else,
					stmt_id, pc, state);
	}

	if ((!is_nested_allowed(cond, tree->u.i.then_body) ||
	     (has_else && !is_nested_allowed(cond, tree->u.i.else_body)))) {
		isl_pw_aff_free(cond);
		return scop_from_non_affine_if(tree, scop_then, scop_else,
					stmt_id, pc, state);
	}

	pet_context_free(pc);
	return scop_from_affine_if(tree, cond, scop_then, scop_else, state);
}

/* Return a one-dimensional multi piecewise affine expression that is equal
 * to the constant 1 and is defined over a zero-dimensional domain.
 */
static __isl_give isl_multi_pw_aff *one_mpa(isl_ctx *ctx)
{
	isl_space *space;
	isl_local_space *ls;
	isl_aff *aff;

	space = isl_space_set_alloc(ctx, 0, 0);
	ls = isl_local_space_from_space(space);
	aff = isl_aff_zero_on_domain(ls);
	aff = isl_aff_set_constant_si(aff, 1);

	return isl_multi_pw_aff_from_pw_aff(isl_pw_aff_from_aff(aff));
}

/* Construct a pet_scop for a continue statement.
 *
 * We simply create an empty scop with a universal pet_skip_now
 * skip condition.  This skip condition will then be taken into
 * account by the enclosing loop construct, possibly after
 * being incorporated into outer skip conditions.
 */
static struct pet_scop *scop_from_continue(__isl_keep pet_tree *tree)
{
	struct pet_scop *scop;
	isl_ctx *ctx;

	ctx = pet_tree_get_ctx(tree);
	scop = pet_scop_empty(ctx);
	if (!scop)
		return NULL;

	scop = pet_scop_set_skip(scop, pet_skip_now, one_mpa(ctx));

	return scop;
}

/* Construct a pet_scop for a break statement.
 *
 * We simply create an empty scop with both a universal pet_skip_now
 * skip condition and a universal pet_skip_later skip condition.
 * These skip conditions will then be taken into
 * account by the enclosing loop construct, possibly after
 * being incorporated into outer skip conditions.
 */
static struct pet_scop *scop_from_break(__isl_keep pet_tree *tree)
{
	struct pet_scop *scop;
	isl_ctx *ctx;
	isl_multi_pw_aff *skip;

	ctx = pet_tree_get_ctx(tree);
	scop = pet_scop_empty(ctx);
	if (!scop)
		return NULL;

	skip = one_mpa(ctx);
	scop = pet_scop_set_skip(scop, pet_skip_now,
				    isl_multi_pw_aff_copy(skip));
	scop = pet_scop_set_skip(scop, pet_skip_later, skip);

	return scop;
}

/* Extract a clone of the kill statement in "scop".
 * "scop" is expected to have been created from a DeclStmt
 * and should have the kill as its first statement.
 */
static struct pet_scop *extract_kill(isl_ctx *ctx, struct pet_scop *scop,
	struct pet_state *state)
{
	pet_expr *kill;
	struct pet_stmt *stmt;
	isl_multi_pw_aff *index;
	isl_map *access;
	pet_expr *arg;

	if (!scop)
		return NULL;
	if (scop->n_stmt < 1)
		isl_die(ctx, isl_error_internal,
			"expecting at least one statement", return NULL);
	stmt = scop->stmts[0];
	if (!pet_stmt_is_kill(stmt))
		isl_die(ctx, isl_error_internal,
			"expecting kill statement", return NULL);

	arg = pet_expr_get_arg(stmt->body, 0);
	index = pet_expr_access_get_index(arg);
	access = pet_expr_access_get_access(arg);
	pet_expr_free(arg);
	index = isl_multi_pw_aff_reset_tuple_id(index, isl_dim_in);
	access = isl_map_reset_tuple_id(access, isl_dim_in);
	kill = pet_expr_kill_from_access_and_index(access, index);
	stmt = pet_stmt_from_pet_expr(pet_loc_copy(stmt->loc),
					NULL, state->n_stmt++, kill);
	return pet_scop_from_pet_stmt(ctx, stmt);
}

/* Mark all arrays in "scop" as being exposed.
 */
static struct pet_scop *mark_exposed(struct pet_scop *scop)
{
	int i;

	if (!scop)
		return NULL;
	for (i = 0; i < scop->n_array; ++i)
		scop->arrays[i]->exposed = 1;
	return scop;
}

/* Try and construct a pet_scop corresponding to (part of)
 * a sequence of statements within the context "pc".
 *
 * After extracting a statement, we update "pc"
 * based on the top-level assignments in the statement
 * so that we can exploit them in subsequent statements in the same block.
 *
 * If there are any breaks or continues in the individual statements,
 * then we may have to compute a new skip condition.
 * This is handled using a pet_skip_info object.
 * On initialization, the object checks if skip conditions need
 * to be computed.  If so, it does so in pet_skip_info_seq_extract and
 * adds them in pet_skip_info_seq_add.
 *
 * If "block" is set, then we need to insert kill statements at
 * the end of the block for any array that has been declared by
 * one of the statements in the sequence.  Each of these declarations
 * results in the construction of a kill statement at the place
 * of the declaration, so we simply collect duplicates of
 * those kill statements and append these duplicates to the constructed scop.
 *
 * If "block" is not set, then any array declared by one of the statements
 * in the sequence is marked as being exposed.
 *
 * If autodetect is set, then we allow the extraction of only a subrange
 * of the sequence of statements.  However, if there is at least one statement
 * for which we could not construct a scop and the final range contains
 * either no statements or at least one kill, then we discard the entire
 * range.
 */
static struct pet_scop *scop_from_block(__isl_keep pet_tree *tree,
	__isl_keep pet_context *pc, struct pet_state *state)
{
	int i;
	isl_ctx *ctx;
	struct pet_scop *scop, *kills;

	ctx = pet_tree_get_ctx(tree);

	pc = pet_context_copy(pc);
	scop = pet_scop_empty(ctx);
	kills = pet_scop_empty(ctx);
	for (i = 0; i < tree->u.b.n; ++i) {
		struct pet_scop *scop_i;

		scop_i = scop_from_tree(tree->u.b.child[i], pc, state);
		pc = scop_handle_writes(scop_i, pc);
		struct pet_skip_info skip;
		pet_skip_info_seq_init(&skip, ctx, scop, scop_i);
		pet_skip_info_seq_extract(&skip, state);
		if (pet_skip_info_has_skip(&skip))
			scop_i = pet_scop_prefix(scop_i, 0);
		if (scop_i && pet_tree_is_decl(tree->u.b.child[i])) {
			if (tree->u.b.block) {
				struct pet_scop *kill;
				kill = extract_kill(ctx, scop_i, state);
				kills = pet_scop_add_par(ctx, kills, kill);
			} else
				scop_i = mark_exposed(scop_i);
		}
		scop_i = pet_scop_prefix(scop_i, i);
		scop = pet_scop_add_seq(ctx, scop, scop_i);

		scop = pet_skip_info_seq_add(&skip, scop, i);

		if (!scop)
			break;
	}

	kills = pet_scop_prefix(kills, tree->u.b.n);
	scop = pet_scop_add_seq(ctx, scop, kills);

	pet_context_free(pc);

	return scop;
}

/* Construct a pet_scop that corresponds to the pet_tree "tree"
 * within the context "pc" by calling the appropriate function
 * based on the type of "tree".
 */
static struct pet_scop *scop_from_tree(__isl_keep pet_tree *tree,
	__isl_keep pet_context *pc, struct pet_state *state)
{
	if (!tree)
		return NULL;

	switch (tree->type) {
	case pet_tree_error:
		return NULL;
	case pet_tree_block:
		return scop_from_block(tree, pc, state);
	case pet_tree_break:
		return scop_from_break(tree);
	case pet_tree_continue:
		return scop_from_continue(tree);
	case pet_tree_decl:
	case pet_tree_decl_init:
		return scop_from_decl(tree, pc, state);
	case pet_tree_expr:
		return scop_from_expr(pet_expr_copy(tree->u.e.expr),
					isl_id_copy(tree->label),
					state->n_stmt++,
					pet_tree_get_loc(tree), pc);
	case pet_tree_if:
	case pet_tree_if_else:
		return scop_from_if(tree, pc, state);
	case pet_tree_for:
		return scop_from_for(tree, pc, state);
	case pet_tree_while:
		return scop_from_while(tree, pc, state);
	case pet_tree_infinite_loop:
		return scop_from_infinite_for(tree, pc, state);
	}

	isl_die(tree->ctx, isl_error_internal, "unhandled type",
		return NULL);
}

/* Construct a pet_scop that corresponds to the pet_tree "tree".
 * "int_size" is the number of bytes need to represent an integer.
 * "extract_array" is a callback that we can use to create a pet_array
 * that corresponds to the variable accessed by an expression.
 *
 * Initialize the global state, construct a context and then
 * construct the pet_scop by recursively visiting the tree.
 */
struct pet_scop *pet_scop_from_pet_tree(__isl_take pet_tree *tree, int int_size,
	struct pet_array *(*extract_array)(__isl_keep pet_expr *access,
		__isl_keep pet_context *pc, void *user), void *user,
	__isl_keep pet_context *pc)
{
	struct pet_scop *scop;
	struct pet_state state = { 0 };

	if (!tree)
		return NULL;

	state.ctx = pet_tree_get_ctx(tree);
	state.int_size = int_size;
	state.extract_array = extract_array;
	state.user = user;

	scop = scop_from_tree(tree, pc, &state);
	scop = pet_scop_set_loc(scop, pet_tree_get_loc(tree));

	pet_tree_free(tree);

	return scop;
}
