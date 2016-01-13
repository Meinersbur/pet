/*
 * Copyright 2011      Leiden University. All rights reserved.
 * Copyright 2015      Sven Verdoolaege. All rights reserved.
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

#include "clang.h"
#include "expr.h"
#include "id.h"
#include "inliner.h"

using namespace std;
using namespace clang;

/* Add an assignment of "expr" to a variable with identifier "id" and
 * type "qt" and return a pet_expr corresponding to the assigned variable.
 */
__isl_give pet_expr *pet_inliner::assign( __isl_take isl_id *id, QualType qt,
	__isl_take pet_expr *expr)
{
	int type_size;
	pet_expr *var;

	var = pet_id_create_index_expr(id);
	type_size = pet_clang_get_type_size(qt, ast_context);
	var = pet_expr_set_type_size(var, type_size);

	assignments.push_back(pair<pet_expr *, pet_expr *>(var, expr));

	return pet_expr_copy(var);
}

/* Add a scalar argument to the inliner.
 * "decl" is the declaration of the formal argument.
 * "name" is the name that should be used in the assignment before
 * the inlined tree.
 * "expr" is the actual argument.
 *
 * Create an identifier called "name" referring to "decl".
 * Assign it the value of "expr" and keep track of
 * the substitution of the identifier corresponding to "decl" by
 * the expression that is assigned the value.
 */
void pet_inliner::add_scalar_arg(ValueDecl *decl, const string &name,
	__isl_take pet_expr *expr)
{
	QualType type = decl->getType();
	isl_id *id;
	pet_expr *var;

	id = pet_id_from_name_and_decl(ctx, name.c_str(), decl);
	var = assign(id, type, expr);
	id = pet_id_from_decl(ctx, decl);
	add_sub(id, var);
}

/* Add an array argument to the inliner.
 * "decl" is the declaration of the formal argument.
 * "expr" is the actual argument and is and access expression.
 * "is_addr" is set if it is the address of "expr" that is passed
 * as an argument.
 *
 * Create identifiers for the arguments of "expr".
 * Assign each of them the value of the corresponding argument and
 * replace the argument by the expression that is assigned the value.
 * Keep track of the substitution of the identifier corresponding
 * to "decl" by the resulting expression.
 */
void pet_inliner::add_array_arg(ValueDecl *decl, __isl_take pet_expr *expr,
	int is_addr)
{
	isl_id *id;

	for (int j = 0; j < expr->n_arg; ++j) {
		pet_expr *var;
		QualType type = ast_context.IntTy;

		id = pet_id_arg_from_type(ctx, n_arg++, type);
		var = assign(id, type, pet_expr_copy(expr->args[j]));
		expr = pet_expr_set_arg(expr, j, var);
	}
	if (is_addr)
		expr = pet_expr_new_unary(0, pet_op_address_of, expr);
	id = pet_id_from_decl(ctx, decl);
	add_sub(id, expr);
}

/* Inline "tree" by applying the substitutions to "tree" and placing
 * the result in a block after the assignments stored in "assignments".
 */
__isl_give pet_tree *pet_inliner::inline_tree(__isl_take pet_tree *tree)
{
	pet_expr *expr;
	pet_tree *block;
	int n = assignments.size() + 1;

	block = pet_tree_new_block(ctx, 1, n);

	for (int i = 0; i < assignments.size(); ++i) {
		pet_tree *tree_i;

		expr = pet_expr_copy(assignments[i].first);
		expr = pet_expr_access_set_write(expr, 1);
		expr = pet_expr_access_set_read(expr, 0);
		tree_i = pet_tree_new_decl_init(expr,
					pet_expr_copy(assignments[i].second));
		block = pet_tree_block_add_child(block, tree_i);
	}

	tree = substitute(tree);
	block = pet_tree_block_add_child(block, tree);

	return block;
}

/* Free all elements in the assignments.
 */
pet_inliner::~pet_inliner()
{
	std::vector<std::pair<pet_expr *, pet_expr *> >::iterator it;

	for (it = assignments.begin(); it != assignments.end(); ++it) {
		pet_expr_free(it->first);
		pet_expr_free(it->second);
	}
}
