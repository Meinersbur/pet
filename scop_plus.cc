/*
 * Copyright 2011 Leiden University. All rights reserved.
 * Copyright 2013 Ecole Normale Superieure. All rights reserved.
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
#include <vector>

#include "clang.h"
#include "scop_plus.h"

using namespace std;
using namespace clang;

/* And the sequence of nested arrays of structures "ancestors"
 * to "arrays".  The final element in the sequence may be a leaf
 * and may therefore refer to a primitive type rather than a record type.
 *
 * Futhermore, if the innermost array in the sequence is an array of structures
 * then recursively call collect_sub_arrays for all subfields of this
 * structure.
 */
static void collect_sub_arrays(ValueDecl *decl, vector<ValueDecl *> ancestors,
	set<vector<ValueDecl *> > &arrays)
{
	QualType type = decl->getType();
	RecordDecl *record;
	RecordDecl::field_iterator it;

	arrays.insert(ancestors);

	type = pet_clang_base_type(type);

	if (!type->isRecordType())
		return;

	record = pet_clang_record_decl(type);

	for (it = record->field_begin(); it != record->field_end(); ++it) {
		FieldDecl *field = *it;
		bool anonymous = field->isAnonymousStructOrUnion();

		if (!anonymous)
			ancestors.push_back(field);
		collect_sub_arrays(field, ancestors, arrays);
		if (!anonymous)
			ancestors.pop_back();
	}
}

/* Extract one or more sequences of declarations from the access expression
 * "expr" and them to "arrays".
 *
 * If "expr" represents an array access, then the extracted sequence
 * contains a single element corresponding to the array declaration.
 * Otherwise, if "expr" represents a member access, then the extracted
 * sequences contain an element for the outer array of structures and
 * for each nested array or scalar.  One such sequence is (recursively)
 * added for each member of the accessed outer array.
 *
 * If the array being accessed has a NULL ValueDecl, then it
 * is a virtual scalar.  We don't need to collect such scalars
 * because they are added to the scop of the statement writing
 * to the scalar.
 */
static void access_collect_arrays(struct pet_expr *expr,
	set<vector<ValueDecl *> > &arrays)
{
	isl_id *id;
	isl_space *space;
	ValueDecl *decl;
	vector<ValueDecl *> ancestors;

	if (pet_expr_is_affine(expr))
		return;

	space = isl_map_get_space(expr->acc.access);
	space = isl_space_range(space);

	while (space && isl_space_is_wrapping(space))
		space = isl_space_domain(isl_space_unwrap(space));

	id = isl_space_get_tuple_id(space, isl_dim_set);
	isl_space_free(space);
	if (!id)
		return;

	decl = (ValueDecl *)isl_id_get_user(id);
	isl_id_free(id);

	if (!decl)
		return;

	ancestors.push_back(decl);
	collect_sub_arrays(decl, ancestors, arrays);
}

static void expr_collect_arrays(struct pet_expr *expr,
	set<vector<ValueDecl *> > &arrays)
{
	if (!expr)
		return;

	for (int i = 0; i < expr->n_arg; ++i)
		expr_collect_arrays(expr->args[i], arrays);

	if (expr->type == pet_expr_access)
		access_collect_arrays(expr, arrays);
}

static void stmt_collect_arrays(struct pet_stmt *stmt,
	set<vector<ValueDecl *> > &arrays)
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
 *
 * Each accessed array is represented by a sequence of nested
 * array declarations, one for the outer array of structures
 * and one for each member access.
 *
 * The arrays that already appear in scop->arrays are assumed
 * to be simple arrays, represented by a sequence of a single element.
 */
void pet_scop_collect_arrays(struct pet_scop *scop,
	set<vector<ValueDecl *> > &arrays)
{
	if (!scop)
		return;

	for (int i = 0; i < scop->n_stmt; ++i)
		stmt_collect_arrays(scop->stmts[i], arrays);

	for (int i = 0; i < scop->n_array; ++i) {
		ValueDecl *decl;
		vector<ValueDecl *> ancestors;

		isl_id *id = isl_set_get_tuple_id(scop->arrays[i]->extent);
		decl = (ValueDecl *)isl_id_get_user(id);
		isl_id_free(id);

		ancestors.push_back(decl);

		arrays.erase(ancestors);
	}
}
