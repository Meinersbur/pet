/*
 * Copyright 2011 Leiden University. All rights reserved.
 * Copyright 2012-2013 Ecole Normale Superieure. All rights reserved.
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
#include <isl/ast.h>
#include <pet.h>

/* Print the access expression "expr" to "p".
 *
 * We look up the corresponding isl_ast_expr in "ref2expr"
 * and print that to "p".
 */
static __isl_give isl_printer *print_access(__isl_take isl_printer *p,
	struct pet_expr *expr, __isl_keep isl_id_to_ast_expr *ref2expr)
{
	isl_ast_expr *ast_expr;
	int is_access;

	if (!isl_id_to_ast_expr_has(ref2expr, expr->acc.ref_id))
		isl_die(isl_printer_get_ctx(p), isl_error_internal,
			"missing expression", return isl_printer_free(p));

	ast_expr = isl_id_to_ast_expr_get(ref2expr,
					isl_id_copy(expr->acc.ref_id));
	is_access = isl_ast_expr_get_type(ast_expr) == isl_ast_expr_op &&
		isl_ast_expr_get_op_type(ast_expr) == isl_ast_op_access;
	if (!is_access)
		p = isl_printer_print_str(p, "(");
	p = isl_printer_print_ast_expr(p, ast_expr);
	if (!is_access)
		p = isl_printer_print_str(p, ")");
	isl_ast_expr_free(ast_expr);

	return p;
}

/* Is "op" a postfix operator?
 */
static int is_postfix(enum pet_op_type op)
{
	switch (op) {
	case pet_op_post_inc:
	case pet_op_post_dec:
		return 1;
	default:
		return 0;
	}
}

/* Print "expr" to "p".
 *
 * If "outer" is set, then we are printing the outer expression statement.
 *
 * The access subexpressions are replaced by the isl_ast_expr
 * associated to its reference identifier in "ref2expr".
 */
static __isl_take isl_printer *print_pet_expr(__isl_take isl_printer *p,
	struct pet_expr *expr, int outer,
	__isl_keep isl_id_to_ast_expr *ref2expr)
{
	int i;

	switch (expr->type) {
	case pet_expr_double:
		p = isl_printer_print_str(p, expr->d.s);
		break;
	case pet_expr_access:
		p = print_access(p, expr, ref2expr);
		break;
	case pet_expr_unary:
		if (!outer)
			p = isl_printer_print_str(p, "(");
		if (!is_postfix(expr->op))
			p = isl_printer_print_str(p, pet_op_str(expr->op));
		p = print_pet_expr(p, expr->args[pet_un_arg], 0, ref2expr);
		if (is_postfix(expr->op))
			p = isl_printer_print_str(p, pet_op_str(expr->op));
		if (!outer)
			p = isl_printer_print_str(p, ")");
		break;
	case pet_expr_binary:
		if (!outer)
			p = isl_printer_print_str(p, "(");
		p = print_pet_expr(p, expr->args[pet_bin_lhs], 0,
					ref2expr);
		p = isl_printer_print_str(p, " ");
		p = isl_printer_print_str(p, pet_op_str(expr->op));
		p = isl_printer_print_str(p, " ");
		p = print_pet_expr(p, expr->args[pet_bin_rhs], 0,
					ref2expr);
		if (!outer)
			p = isl_printer_print_str(p, ")");
		break;
	case pet_expr_ternary:
		if (!outer)
			p = isl_printer_print_str(p, "(");
		p = print_pet_expr(p, expr->args[pet_ter_cond], 0,
					ref2expr);
		p = isl_printer_print_str(p, " ? ");
		p = print_pet_expr(p, expr->args[pet_ter_true], 0,
					ref2expr);
		p = isl_printer_print_str(p, " : ");
		p = print_pet_expr(p, expr->args[pet_ter_false], 0,
					ref2expr);
		if (!outer)
			p = isl_printer_print_str(p, ")");
		break;
	case pet_expr_call:
		p = isl_printer_print_str(p, expr->name);
		p = isl_printer_print_str(p, "(");
		for (i = 0; i < expr->n_arg; ++i) {
			if (i)
				p = isl_printer_print_str(p, ", ");
			p = print_pet_expr(p, expr->args[i], 1, ref2expr);
		}
		p = isl_printer_print_str(p, ")");
		break;
	case pet_expr_cast:
		if (!outer)
			p = isl_printer_print_str(p, "(");
		p = isl_printer_print_str(p, "(");
		p = isl_printer_print_str(p, expr->type_name);
		p = isl_printer_print_str(p, ") ");
		p = print_pet_expr(p, expr->args[0], 0, ref2expr);
		if (!outer)
			p = isl_printer_print_str(p, ")");
		break;
	}

	return p;
}

/* Print "stmt" to "p".
 *
 * The access expressions in "stmt" are replaced by the isl_ast_expr
 * associated to its reference identifier in "ref2expr".
 */
__isl_give isl_printer *pet_stmt_print_body(struct pet_stmt *stmt,
	__isl_take isl_printer *p, __isl_keep isl_id_to_ast_expr *ref2expr)
{
	if (!stmt)
		return isl_printer_free(p);
	p = isl_printer_start_line(p);
	p = print_pet_expr(p, stmt->body, 1, ref2expr);
	p = isl_printer_print_str(p, ";");
	p = isl_printer_end_line(p);

	return p;
}
