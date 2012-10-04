/*
 * Copyright 2011 Leiden University. All rights reserved.
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

#include <set>

#include "scop_plus.h"

using namespace std;
using namespace clang;

/* If the array being accessed has a NULL ValueDecl, then it
 * is a virtual scalar.  We don't need to collect such scalars
 * because they are added to the scop of the statement writing
 * to the scalar.
 */
static void access_collect_arrays(struct pet_expr *expr,
	set<ValueDecl *> &arrays)
{
	isl_id *id;
	ValueDecl *decl;

	if (!isl_map_has_tuple_id(expr->acc.access, isl_dim_out))
		return;
	id = isl_map_get_tuple_id(expr->acc.access, isl_dim_out);
	if (!id)
		return;

	decl = (ValueDecl *)isl_id_get_user(id);
	isl_id_free(id);

	if (decl)
		arrays.insert(decl);
}

static void expr_collect_arrays(struct pet_expr *expr, set<ValueDecl *> &arrays)
{
	if (!expr)
		return;

	for (int i = 0; i < expr->n_arg; ++i)
		expr_collect_arrays(expr->args[i], arrays);

	if (expr->type == pet_expr_access)
		access_collect_arrays(expr, arrays);
}

static void stmt_collect_arrays(struct pet_stmt *stmt, set<ValueDecl *> &arrays)
{
	if (!stmt)
		return;

	for (int i = 0; i < stmt->n_arg; ++i)
		expr_collect_arrays(stmt->args[i], arrays);

	expr_collect_arrays(stmt->body, arrays);
}

/* Collect the set of all accessed arrays (or scalars) in "scop",
 * except those that already appear in scop->arrays,
 * and put them in "arrays".
 */
void pet_scop_collect_arrays(struct pet_scop *scop, set<ValueDecl *> &arrays)
{
	if (!scop)
		return;

	for (int i = 0; i < scop->n_stmt; ++i)
		stmt_collect_arrays(scop->stmts[i], arrays);

	for (int i = 0; i < scop->n_array; ++i) {
		ValueDecl *decl;
		isl_id *id = isl_set_get_tuple_id(scop->arrays[i]->extent);
		decl = (ValueDecl *)isl_id_get_user(id);
		isl_id_free(id);

		arrays.erase(decl);
	}
}
