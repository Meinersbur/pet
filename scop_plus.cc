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
#include "expr.h"
#include "id.h"
#include "scop_plus.h"
#include "tree.h"

using namespace std;
using namespace clang;

/* Add the sequence of nested arrays of structures represented by "ancestors"
 * to "arrays".  The final element in the sequence may be a leaf
 * and may therefore refer to a primitive type rather than a record type.
 *
 * Futhermore, if the innermost array in the sequence is an array of structures
 * then recursively call collect_sub_arrays for all subfields of this
 * structure.
 */
static void collect_sub_arrays(ValueDecl *decl,
	__isl_keep isl_id_list *ancestors, array_desc_set &arrays)
{
	isl_ctx *ctx;
	QualType type = decl->getType();
	RecordDecl *record;
	RecordDecl::field_iterator it;

	arrays.insert(isl_id_list_copy(ancestors));

	type = pet_clang_base_type(type);

	if (!type->isRecordType())
		return;

	record = pet_clang_record_decl(type);

	ctx = isl_id_list_get_ctx(ancestors);
	for (it = record->field_begin(); it != record->field_end(); ++it) {
		FieldDecl *field = *it;
		bool anonymous = field->isAnonymousStructOrUnion();
		isl_id_list *extended;

		extended = isl_id_list_copy(ancestors);
		if (!anonymous) {
			isl_id *id = pet_id_from_decl(ctx, field);
			extended = isl_id_list_add(extended, id);
		}
		collect_sub_arrays(field, extended, arrays);
		isl_id_list_free(extended);
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
static void access_collect_arrays(__isl_keep pet_expr *expr,
	array_desc_set &arrays)
{
	isl_id *id;
	isl_space *space;
	ValueDecl *decl;
	isl_id_list *ancestors;

	if (pet_expr_is_affine(expr))
		return;

	space = pet_expr_access_get_data_space(expr);

	while (space && isl_space_is_wrapping(space))
		space = isl_space_domain(isl_space_unwrap(space));

	id = isl_space_get_tuple_id(space, isl_dim_set);
	isl_space_free(space);
	if (!id)
		return;

	decl = pet_id_get_decl(id);

	if (!decl) {
		isl_id_free(id);
		return;
	}

	ancestors = isl_id_list_from_id(id);
	collect_sub_arrays(decl, ancestors, arrays);
	isl_id_list_free(ancestors);
}

static void expr_collect_arrays(__isl_keep pet_expr *expr,
	array_desc_set &arrays)
{
	int n;

	if (!expr)
		return;

	n = pet_expr_get_n_arg(expr);
	for (int i = 0; i < n; ++i) {
		pet_expr *arg;

		arg = pet_expr_get_arg(expr, i);
		expr_collect_arrays(arg, arrays);
		pet_expr_free(arg);
	}

	if (pet_expr_get_type(expr) == pet_expr_access)
		access_collect_arrays(expr, arrays);
}

/* Wrapper around access_collect_arrays for use as a callback function
 * to pet_tree_foreach_access_expr.
 */
static int access_collect_wrap(__isl_keep pet_expr *expr, void *user)
{
	array_desc_set *arrays = (array_desc_set *) user;

	access_collect_arrays(expr, *arrays);

	return 0;
}

static void stmt_collect_arrays(struct pet_stmt *stmt,
	array_desc_set &arrays)
{
	if (!stmt)
		return;

	for (int i = 0; i < stmt->n_arg; ++i)
		expr_collect_arrays(stmt->args[i], arrays);

	pet_tree_foreach_access_expr(stmt->body, &access_collect_wrap, &arrays);
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
	array_desc_set &arrays)
{
	if (!scop)
		return;

	for (int i = 0; i < scop->n_stmt; ++i)
		stmt_collect_arrays(scop->stmts[i], arrays);

	for (int i = 0; i < scop->n_array; ++i) {
		ValueDecl *decl;
		isl_id_list *ancestors;

		isl_id *id = isl_set_get_tuple_id(scop->arrays[i]->extent);
		decl = pet_id_get_decl(id);

		if (!decl) {
			isl_id_free(id);
			continue;
		}

		ancestors = isl_id_list_from_id(id);
		arrays.erase(ancestors);
		isl_id_list_free(ancestors);
	}
}
