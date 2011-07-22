#include <set>

#include "scop_plus.h"

using namespace std;
using namespace clang;

static void access_collect_arrays(struct pet_expr *expr,
	set<ValueDecl *> &arrays)
{
	isl_id *id;
	ValueDecl *decl;

	id = isl_map_get_tuple_id(expr->acc.access, isl_dim_out);
	if (!id)
		return;

	decl = (ValueDecl *)isl_id_get_user(id);
	isl_id_free(id);

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
	expr_collect_arrays(stmt->body, arrays);
}

/* Collect the set of all accessed arrays (or scalars) in "scop"
 * and put them in "arrays".
 */
void pet_scop_collect_arrays(struct pet_scop *scop, set<ValueDecl *> &arrays)
{
	if (!scop)
		return;

	for (int i = 0; i < scop->n_stmt; ++i)
		stmt_collect_arrays(scop->stmts[i], arrays);
}
