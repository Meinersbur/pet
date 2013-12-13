/*
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
 * THIS SOFTWARE IS PROVIDED BY ECOLE NORMALE SUPERIEURE ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL ECOLE NORMALE SUPERIEURE OR
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
 * Ecole Normale Superieure.
 */

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <isl/arg.h>
#include <isl/aff.h>
#include <isl/options.h>
#include <isl/set.h>
#include <isl/union_map.h>
#include <isl/id_to_pw_aff.h>
#include <pet.h>

#include "aff.h"

struct options {
	struct isl_options	*isl;
	struct pet_options	*pet;
	char *schedule;
	char *code;
};

ISL_ARGS_START(struct options, options_args)
ISL_ARG_CHILD(struct options, isl, "isl", &isl_options_args, "isl options")
ISL_ARG_CHILD(struct options, pet, NULL, &pet_options_args, "pet options")
ISL_ARG_ARG(struct options, schedule, "schedule", NULL)
ISL_ARG_ARG(struct options, code, "code", NULL)
ISL_ARGS_END

ISL_ARG_DEF(options, struct options, options_args)

static __isl_give isl_pw_aff *expr_extract_pw_aff(__isl_keep pet_expr *expr,
	__isl_keep isl_space *space, __isl_keep isl_id_to_pw_aff *assignments);

/* Extract an affine expression from the call to floord in "expr",
 * possibly exploiting "assignments".
 *
 * "space" is the iteration space of the statement containing the expression.
 */
static __isl_give isl_pw_aff *expr_extract_floord(__isl_keep pet_expr *expr,
	__isl_keep isl_space *space, __isl_keep isl_id_to_pw_aff *assignments)
{
	isl_pw_aff *lhs, *rhs;
	pet_expr *arg;

	arg = pet_expr_get_arg(expr, 0);
	lhs = expr_extract_pw_aff(arg, space, assignments);
	pet_expr_free(arg);
	arg = pet_expr_get_arg(expr, 1);
	rhs = expr_extract_pw_aff(arg, space, assignments);
	pet_expr_free(arg);
	return isl_pw_aff_floor(isl_pw_aff_div(lhs, rhs));
}

/* Extract an affine expression from the call in "expr",
 * possibly exploiting "assignments".
 *
 * "space" is the iteration space of the statement containing the expression.
 *
 * We only support calls to the "floord" function for now.
 */
static __isl_give isl_pw_aff *call_expr_extract_pw_aff(
	__isl_keep pet_expr *expr, __isl_keep isl_space *space,
	__isl_keep isl_id_to_pw_aff *assignments)
{
	const char *name;

	name = pet_expr_call_get_name(expr);
	if (!name)
		return NULL;
	if (!strcmp(name, "floord"))
		return expr_extract_floord(expr, space, assignments);

	isl_die(isl_id_to_pw_aff_get_ctx(assignments), isl_error_unsupported,
		"unsupported expression", return NULL);
}

/* Is the variable accessed by "index" assigned in "assignments"?
 *
 * The assignments map variable identifiers to functions of the form
 *
 *	{ domain -> value }
 */
static int is_assigned(__isl_keep isl_multi_pw_aff *index,
	__isl_keep isl_id_to_pw_aff *assignments)
{
	isl_id *var;
	int assigned;

	var = isl_multi_pw_aff_get_tuple_id(index, isl_dim_out);
	assigned = isl_id_to_pw_aff_has(assignments, var);
	isl_id_free(var);

	return assigned;
}

/* Apply the appropriate assignment in "assignments"
 * to the index expression "index".
 *
 * "index" is of the form
 *
 *	{ access_domain -> variable }
 *
 * "assignments" maps variable identifiers to functions of the form
 *
 *	{ assignment_domain -> value }
 *
 * We assume the assignment precedes the access in the code.
 * In particular, we assume that the loops around the assignment
 * are the same as the first loops around the access.
 *
 * We compute
 *
 *	{ access_domain -> assignment_domain }
 *
 * equating the iterators of assignment_domain to the corresponding iterators
 * in access_domain and then plug that into the assigned value, obtaining
 *
 *	{ access_domain -> value }
 */
static __isl_give isl_pw_aff *apply_assignment(
	__isl_take isl_multi_pw_aff *index,
	__isl_keep isl_id_to_pw_aff *assignments)
{
	isl_id *id;
	isl_set *dom;
	isl_pw_aff *val;
	isl_multi_aff *ma;
	isl_space *space, *dom_space;
	isl_local_space *ls;
	int i, n;

	id = isl_multi_pw_aff_get_tuple_id(index, isl_dim_out);
	dom = isl_multi_pw_aff_domain(index);
	val = isl_id_to_pw_aff_get(assignments, id);
	space = isl_pw_aff_get_domain_space(val);
	dom_space = isl_set_get_space(dom);
	space = isl_space_map_from_domain_and_range(dom_space, space);
	ma = isl_multi_aff_zero(space);
	ls = isl_local_space_from_space(isl_set_get_space(dom));
	n = isl_multi_aff_dim(ma, isl_dim_out);
	for (i = 0; i < n; ++i) {
		isl_aff *aff;

		aff = isl_aff_var_on_domain(isl_local_space_copy(ls),
					isl_dim_set, i);
		ma = isl_multi_aff_set_aff(ma, i, aff);
	}
	isl_local_space_free(ls);

	val = isl_pw_aff_pullback_multi_aff(val, ma);
	val = isl_pw_aff_intersect_domain(val, dom);

	return val;
}

/* Extract an affine expression from the access to a named space in "index",
 * possibly exploiting "assignments".
 *
 * If the variable has been assigned a value, we return the corresponding
 * assignment.  Otherwise, we assume we are accessing a 0D space and
 * we turn that into an expression equal to a parameter of the same name.
 */
static __isl_give isl_pw_aff *resolve_access(__isl_take isl_multi_pw_aff *index,
	__isl_keep isl_id_to_pw_aff *assignments)
{
	isl_id *id;
	isl_set *dom;
	isl_aff *aff;
	isl_local_space *ls;
	isl_pw_aff *pa;

	if (is_assigned(index, assignments))
		return apply_assignment(index, assignments);

	id = isl_multi_pw_aff_get_tuple_id(index, isl_dim_out);
	dom = isl_multi_pw_aff_domain(index);
	dom = isl_set_insert_dims(dom, isl_dim_param, 0, 1);
	dom = isl_set_set_dim_id(dom, isl_dim_param, 0, id);
	ls = isl_local_space_from_space(isl_set_get_space(dom));
	aff = isl_aff_var_on_domain(ls, isl_dim_param, 0);
	pa = isl_pw_aff_alloc(dom, aff);

	return pa;
}

/* Extract an affine expression from the access expression "expr",
 * possibly exploiting "assignments".
 *
 * If we are accessing a (1D) anonymous space, then we are actually
 * computing an affine expression and we simply return that expression.
 * Otherwise, we try and convert the access to an affine expression in
 * resolve_access().
 */
static __isl_give isl_pw_aff *access_expr_extract_pw_aff(
	__isl_keep pet_expr *expr, __isl_keep isl_id_to_pw_aff *assignments)
{
	isl_pw_aff *pa;
	isl_multi_pw_aff *index;

	index = pet_expr_access_get_index(expr);
	if (isl_multi_pw_aff_has_tuple_id(index, isl_dim_out)) {
		pa = resolve_access(index, assignments);
	} else {
		pa = isl_multi_pw_aff_get_pw_aff(index, 0);
		isl_multi_pw_aff_free(index);
	}
	return pa;
}

/* Extract an affine expression defined over iteration space "space"
 * from the integer expression "expr".
 */
static __isl_give isl_pw_aff *int_expr_extract_pw_aff(
	__isl_keep  pet_expr *expr, __isl_keep isl_space *space)
{
	isl_local_space *ls;
	isl_aff *aff;

	ls = isl_local_space_from_space(isl_space_copy(space));
	aff = isl_aff_zero_on_domain(ls);
	aff = isl_aff_add_constant_val(aff, pet_expr_int_get_val(expr));
	return isl_pw_aff_from_aff(aff);
}

/* Extract an affine expression from the operation in "expr",
 * possibly exploiting "assignments".
 *
 * "space" is the iteration space of the statement containing the expression.
 *
 * We only handle the kinds of expressions that we would expect
 * as arguments to a function call in code generated by isl.
 */
static __isl_give isl_pw_aff *op_expr_extract_pw_aff(__isl_keep pet_expr *expr,
	__isl_keep isl_space *space, __isl_keep isl_id_to_pw_aff *assignments)
{
	isl_pw_aff *pa, *pa1, *pa2;
	pet_expr *arg;
	enum pet_op_type type;

	switch (pet_expr_get_n_arg(expr)) {
	case 1:
		if (pet_expr_op_get_type(expr) == pet_op_minus) {
			arg = pet_expr_get_arg(expr, 0);
			pa = expr_extract_pw_aff(arg, space, assignments);
			pet_expr_free(arg);
			return isl_pw_aff_neg(pa);
		}
		assert(0);
	case 2:
		arg = pet_expr_get_arg(expr, 0);
		pa1 = expr_extract_pw_aff(arg, space, assignments);
		pet_expr_free(arg);
		arg = pet_expr_get_arg(expr, 1);
		pa2 = expr_extract_pw_aff(arg, space, assignments);
		pet_expr_free(arg);
		type = pet_expr_op_get_type(expr);
		switch (type) {
		case pet_op_mul:
			pa = isl_pw_aff_mul(pa1, pa2);
			break;
		case pet_op_add:
			pa = isl_pw_aff_add(pa1, pa2);
			break;
		case pet_op_sub:
			pa = isl_pw_aff_sub(pa1, pa2);
			break;
		case pet_op_div:
			pa = isl_pw_aff_tdiv_q(pa1, pa2);
			break;
		case pet_op_mod:
			pa = isl_pw_aff_tdiv_r(pa1, pa2);
			break;
		case pet_op_eq:
		case pet_op_ne:
		case pet_op_le:
		case pet_op_ge:
		case pet_op_lt:
		case pet_op_gt:
			pa = pet_comparison(type, pa1, pa2);
			break;
		case pet_op_land:
		case pet_op_lor:
			pa = pet_boolean(type, pa1, pa2);
			break;
		default:
			assert(0);
		}
		return pa;
	case 3:
		arg = pet_expr_get_arg(expr, 0);
		pa = expr_extract_pw_aff(arg, space, assignments);
		pet_expr_free(arg);
		arg = pet_expr_get_arg(expr, 1);
		pa1 = expr_extract_pw_aff(arg, space, assignments);
		pet_expr_free(arg);
		arg = pet_expr_get_arg(expr, 2);
		pa2 = expr_extract_pw_aff(arg, space, assignments);
		pet_expr_free(arg);
		return isl_pw_aff_cond(pa, pa1, pa2);
	default:
		assert(0);
	}
}

/* Extract an affine expression from "expr", possibly exploiting "assignments",
 * in the form of an isl_pw_aff.
 *
 * "space" is the iteration space of the statement containing the expression.
 *
 * We only handle the kinds of expressions that we would expect
 * as arguments to a function call in code generated by isl.
 */
static __isl_give isl_pw_aff *expr_extract_pw_aff(__isl_keep pet_expr *expr,
	__isl_keep isl_space *space, __isl_keep isl_id_to_pw_aff *assignments)
{
	switch (pet_expr_get_type(expr)) {
	case pet_expr_int:
		return int_expr_extract_pw_aff(expr, space);
	case pet_expr_access:
		return access_expr_extract_pw_aff(expr, assignments);
	case pet_expr_op:
		return op_expr_extract_pw_aff(expr, space, assignments);
	case pet_expr_call:
		return call_expr_extract_pw_aff(expr, space, assignments);
	case pet_expr_cast:
	case pet_expr_double:
	case pet_expr_error:
		assert(0);
	}
}

/* Extract an affine expression from "expr", possibly exploiting "assignments",
 * in the form of an isl_map.
 *
 * "space" is the iteration space of the statement containing the expression.
 */
static __isl_give isl_map *expr_extract_map(__isl_keep pet_expr *expr,
	__isl_keep isl_space *space, __isl_keep isl_id_to_pw_aff *assignments)
{
	isl_pw_aff *pa;

	pa = expr_extract_pw_aff(expr, space, assignments);
	return isl_map_from_pw_aff(pa);
}

/* Extract a call from "stmt", possibly exploiting "assignments".
 *
 * The returned map is of the form
 *
 *	{ domain -> function[arguments] }
 */
static __isl_give isl_map *stmt_extract_call(struct pet_stmt *stmt,
	__isl_keep isl_id_to_pw_aff *assignments)
{
	int i, n;
	isl_set *domain;
	isl_map *call;
	const char *name;

	domain = isl_set_copy(stmt->domain);
	call = isl_map_from_domain(domain);

	assert(pet_expr_get_type(stmt->body) == pet_expr_call);

	n = pet_expr_get_n_arg(stmt->body);
	for (i = 0; i < n; ++i) {
		isl_map *map_i;
		isl_space *space;
		pet_expr *arg;

		arg = pet_expr_get_arg(stmt->body, i);
		space = pet_stmt_get_space(stmt);
		map_i = expr_extract_map(arg, space, assignments);
		isl_space_free(space);
		pet_expr_free(arg);
		call = isl_map_flat_range_product(call, map_i);
	}

	name = pet_expr_call_get_name(stmt->body);
	call = isl_map_set_tuple_name(call, isl_dim_out, name);

	return call;
}

/* Add the assignment in "stmt" to "assignments".
 *
 * We extract the accessed variable identifier "var"
 * and the assigned value
 *
 *	{ domain -> value }
 *
 * and map "var" to this value in "assignments", replacing
 * any possible previously assigned value to the same variable.
 */
static __isl_give isl_id_to_pw_aff *add_assignment(
	__isl_take isl_id_to_pw_aff *assignments, struct pet_stmt *stmt)
{
	isl_id *var;
	isl_space *space;
	isl_pw_aff *val;
	pet_expr *arg;

	assert(pet_stmt_is_assign(stmt));
	arg = pet_expr_get_arg(stmt->body, 0);
	assert(pet_expr_get_type(arg) == pet_expr_access);
	var = pet_expr_access_get_id(arg);
	pet_expr_free(arg);
	arg = pet_expr_get_arg(stmt->body, 1);
	space = pet_stmt_get_space(stmt);
	val = expr_extract_pw_aff(arg, space, assignments);
	isl_space_free(space);
	pet_expr_free(arg);

	assignments = isl_id_to_pw_aff_set(assignments, var, val);

	return assignments;
}

/* Extract a mapping from the iterations domains of "scop" to
 * the calls in the corresponding statements.
 *
 * While scanning "scop", we keep track of assignments to variables
 * so that we can plug them in in the arguments of the calls.
 * Note that we do not perform any dependence analysis on the assigned
 * variables.  In code generated by isl, such assignments should only
 * appear immediately before they are used.
 *
 * The assignments are kept as an associative array between
 * variable identifiers and assignments of the form
 *
 *	{ domain -> value }
 *
 * We skip kill statements.
 * Other than assignments and kill statements, all statements are assumed
 * to be function calls.
 */
static __isl_give isl_union_map *scop_collect_calls(struct pet_scop *scop)
{
	int i;
	isl_ctx *ctx;
	isl_map *call_i;
	isl_id_to_pw_aff *assignments;
	isl_union_map *call;

	if (!scop)
		return NULL;

	call = isl_union_map_empty(isl_set_get_space(scop->context));
	ctx = isl_set_get_ctx(scop->context);
	assignments = isl_id_to_pw_aff_alloc(ctx, 0);

	for (i = 0; i < scop->n_stmt; ++i) {
		struct pet_stmt *stmt;

		stmt = scop->stmts[i];
		if (pet_stmt_is_assign(stmt)) {
			assignments = add_assignment(assignments, stmt);
			continue;
		}
		if (pet_stmt_is_kill(stmt))
			continue;
		call_i = stmt_extract_call(scop->stmts[i], assignments);
		call = isl_union_map_add_map(call, call_i);
	}

	isl_id_to_pw_aff_free(assignments);

	return call;
}

/* Extract a schedule on the original domains from "scop".
 * The original domain elements appear as calls in "scop".
 *
 * We first extract a schedule on the code iteration domains
 * and a mapping from the code iteration domains to the calls
 * (i.e., the original domain) and then combine the two.
 */
static __isl_give isl_union_map *extract_code_schedule(struct pet_scop *scop)
{
	isl_union_map *schedule;
	isl_union_map *calls;

	schedule = pet_scop_collect_schedule(scop);

	calls = scop_collect_calls(scop);

	schedule = isl_union_map_apply_domain(schedule, calls);

	return schedule;
}

/* Check that schedule and code_schedule have the same domain,
 * i.e., that they execute the same statement instances.
 */
static int check_domain(__isl_keep isl_union_map *schedule,
	__isl_keep isl_union_map *code_schedule)
{
	isl_union_set *dom1, *dom2;
	int equal;
	isl_set *s1, *s2;;
	isl_id *id1, *id2;
	int r = 0;

	dom1 = isl_union_map_domain(isl_union_map_copy(schedule));
	dom2 = isl_union_map_domain(isl_union_map_copy(code_schedule));
	equal = isl_union_set_is_equal(dom1, dom2);

	if (equal < 0)
		r =  -1;
	else if (!equal) {
		isl_union_set_dump(dom1);
		isl_union_set_dump(dom2);
		isl_die(isl_union_map_get_ctx(schedule), isl_error_unknown,
			"domains not identical", r = -1);
	}

	isl_union_set_free(dom1);
	isl_union_set_free(dom2);

	return r;
}

/* Check that the relative order specified by the input schedule is respected
 * by the schedule extracted from the code, in case the original schedule
 * is single valued.
 *
 * In particular, check that there is no pair of statement instances
 * such that the first should be scheduled _before_ the second,
 * but is actually scheduled _after_ the second in the code.
 */
static int check_order_sv(__isl_keep isl_union_map *schedule,
	__isl_keep isl_union_map *code_schedule)
{
	isl_union_map *t1;
	isl_union_map *t2;
	int empty;

	t1 = isl_union_map_lex_lt_union_map(isl_union_map_copy(schedule),
					    isl_union_map_copy(schedule));
	t2 = isl_union_map_lex_gt_union_map(isl_union_map_copy(code_schedule),
					    isl_union_map_copy(code_schedule));
	t1 = isl_union_map_intersect(t1, t2);
	empty = isl_union_map_is_empty(t1);
	isl_union_map_free(t1);

	if (empty < 0)
		return -1;
	if (!empty)
		isl_die(isl_union_map_get_ctx(schedule), isl_error_unknown,
			"order not respected", return -1);

	return 0;
}

/* Check that the relative order specified by the input schedule is respected
 * by the schedule extracted from the code, in case the original schedule
 * is not single valued.
 *
 * In particular, check that the order imposed by the schedules on pairs
 * of statement instances is the same.
 */
static int check_order_not_sv(__isl_keep isl_union_map *schedule,
	__isl_keep isl_union_map *code_schedule)
{
	isl_union_map *t1;
	isl_union_map *t2;
	int equal;

	t1 = isl_union_map_lex_lt_union_map(isl_union_map_copy(schedule),
					    isl_union_map_copy(schedule));
	t2 = isl_union_map_lex_lt_union_map(isl_union_map_copy(code_schedule),
					    isl_union_map_copy(code_schedule));
	equal = isl_union_map_is_equal(t1, t2);
	isl_union_map_free(t1);
	isl_union_map_free(t2);

	if (equal < 0)
		return -1;
	if (!equal)
		isl_die(isl_union_map_get_ctx(schedule), isl_error_unknown,
			"order not respected", return -1);

	return 0;
}

/* Check that the relative order specified by the input schedule is respected
 * by the schedule extracted from the code.
 *
 * "sv" indicated whether the original schedule is single valued.
 * If so, we use a cheaper test.  Otherwise, we fall back on a more
 * expensive test.
 */
static int check_order(__isl_keep isl_union_map *schedule,
	__isl_keep isl_union_map *code_schedule, int sv)
{
	if (sv)
		return check_order_sv(schedule, code_schedule);
	else
		return check_order_not_sv(schedule, code_schedule);
}

/* If the original schedule was single valued ("sv" is set),
 * then the schedule extracted from the code should be single valued as well.
 */
static int check_single_valued(__isl_keep isl_union_map *code_schedule, int sv)
{
	if (!sv)
		return 0;

	sv = isl_union_map_is_single_valued(code_schedule);
	if (sv < 0)
		return -1;

	if (!sv)
		isl_die(isl_union_map_get_ctx(code_schedule), isl_error_unknown,
			"schedule not single valued", return -1);

	return 0;
}

/* Read a schedule and a context from the first argument and
 * C code from the second argument and check that the C code
 * corresponds to the schedule on the context.
 *
 * In particular, check that
 * - the domains are identical, i.e., the calls in the C code
 *   correspond to the domain elements of the schedule
 * - no function is called twice with the same arguments, provided
 *   the schedule is single-valued
 * - the calls are performed in an order that is compatible
 *   with the schedule
 *
 * If the schedule is not single-valued then we would have to check
 * that each function with a given set of arguments is called
 * the same number of times as there are images in the schedule,
 * but this is considerably more difficult.
 */
int main(int argc, char **argv)
{
	isl_ctx *ctx;
	isl_set *context;
	isl_union_map *schedule, *code_schedule;
	struct pet_scop *scop;
	struct options *options;
	FILE *file;
	int r;
	int sv;

	options = options_new_with_defaults();
	assert(options);
	ctx = isl_ctx_alloc_with_options(&options_args, options);
	pet_options_set_signed_overflow(ctx, PET_OVERFLOW_IGNORE);
	argc = options_parse(options, argc, argv, ISL_ARG_ALL);

	file = fopen(options->schedule, "r");
	assert(file);
	schedule = isl_union_map_read_from_file(ctx, file);
	context = isl_set_read_from_file(ctx, file);
	fclose(file);

	scop = pet_scop_extract_from_C_source(ctx, options->code, NULL);

	schedule = isl_union_map_intersect_params(schedule,
						isl_set_copy(context));
	code_schedule = extract_code_schedule(scop);
	code_schedule = isl_union_map_intersect_params(code_schedule, context);

	sv = isl_union_map_is_single_valued(schedule);
	r = sv < 0 ||
	    check_domain(schedule, code_schedule) ||
	    check_single_valued(code_schedule, sv) ||
	    check_order(schedule, code_schedule, sv);

	pet_scop_free(scop);
	isl_union_map_free(schedule);
	isl_union_map_free(code_schedule);
	isl_ctx_free(ctx);

	return r;
}
