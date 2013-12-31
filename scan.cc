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

#include <string.h>
#include <set>
#include <map>
#include <iostream>
#include <llvm/Support/raw_ostream.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/ASTDiagnostic.h>
#include <clang/AST/Expr.h>
#include <clang/AST/RecursiveASTVisitor.h>

#include <isl/id.h>
#include <isl/space.h>
#include <isl/aff.h>
#include <isl/set.h>

#include "aff.h"
#include "array.h"
#include "clang.h"
#include "context.h"
#include "expr.h"
#include "expr_arg.h"
#include "nest.h"
#include "options.h"
#include "scan.h"
#include "scop.h"
#include "scop_plus.h"
#include "skip.h"
#include "state.h"
#include "tree.h"
#include "tree2scop.h"

#include "config.h"

using namespace std;
using namespace clang;

static enum pet_op_type UnaryOperatorKind2pet_op_type(UnaryOperatorKind kind)
{
	switch (kind) {
	case UO_Minus:
		return pet_op_minus;
	case UO_Not:
		return pet_op_not;
	case UO_LNot:
		return pet_op_lnot;
	case UO_PostInc:
		return pet_op_post_inc;
	case UO_PostDec:
		return pet_op_post_dec;
	case UO_PreInc:
		return pet_op_pre_inc;
	case UO_PreDec:
		return pet_op_pre_dec;
	default:
		return pet_op_last;
	}
}

static enum pet_op_type BinaryOperatorKind2pet_op_type(BinaryOperatorKind kind)
{
	switch (kind) {
	case BO_AddAssign:
		return pet_op_add_assign;
	case BO_SubAssign:
		return pet_op_sub_assign;
	case BO_MulAssign:
		return pet_op_mul_assign;
	case BO_DivAssign:
		return pet_op_div_assign;
	case BO_Assign:
		return pet_op_assign;
	case BO_Add:
		return pet_op_add;
	case BO_Sub:
		return pet_op_sub;
	case BO_Mul:
		return pet_op_mul;
	case BO_Div:
		return pet_op_div;
	case BO_Rem:
		return pet_op_mod;
	case BO_Shl:
		return pet_op_shl;
	case BO_Shr:
		return pet_op_shr;
	case BO_EQ:
		return pet_op_eq;
	case BO_NE:
		return pet_op_ne;
	case BO_LE:
		return pet_op_le;
	case BO_GE:
		return pet_op_ge;
	case BO_LT:
		return pet_op_lt;
	case BO_GT:
		return pet_op_gt;
	case BO_And:
		return pet_op_and;
	case BO_Xor:
		return pet_op_xor;
	case BO_Or:
		return pet_op_or;
	case BO_LAnd:
		return pet_op_land;
	case BO_LOr:
		return pet_op_lor;
	default:
		return pet_op_last;
	}
}

#if defined(DECLREFEXPR_CREATE_REQUIRES_BOOL)
static DeclRefExpr *create_DeclRefExpr(VarDecl *var)
{
	return DeclRefExpr::Create(var->getASTContext(), var->getQualifierLoc(),
		SourceLocation(), var, false, var->getInnerLocStart(),
		var->getType(), VK_LValue);
}
#elif defined(DECLREFEXPR_CREATE_REQUIRES_SOURCELOCATION)
static DeclRefExpr *create_DeclRefExpr(VarDecl *var)
{
	return DeclRefExpr::Create(var->getASTContext(), var->getQualifierLoc(),
		SourceLocation(), var, var->getInnerLocStart(), var->getType(),
		VK_LValue);
}
#else
static DeclRefExpr *create_DeclRefExpr(VarDecl *var)
{
	return DeclRefExpr::Create(var->getASTContext(), var->getQualifierLoc(),
		var, var->getInnerLocStart(), var->getType(), VK_LValue);
}
#endif

/* Check if the element type corresponding to the given array type
 * has a const qualifier.
 */
static bool const_base(QualType qt)
{
	const Type *type = qt.getTypePtr();

	if (type->isPointerType())
		return const_base(type->getPointeeType());
	if (type->isArrayType()) {
		const ArrayType *atype;
		type = type->getCanonicalTypeInternal().getTypePtr();
		atype = cast<ArrayType>(type);
		return const_base(atype->getElementType());
	}

	return qt.isConstQualified();
}

/* Create an isl_id that refers to the named declarator "decl".
 */
static __isl_give isl_id *create_decl_id(isl_ctx *ctx, NamedDecl *decl)
{
	return isl_id_alloc(ctx, decl->getName().str().c_str(), decl);
}

PetScan::~PetScan()
{
	isl_union_map_free(value_bounds);
}

/* Report a diagnostic, unless autodetect is set.
 */
void PetScan::report(Stmt *stmt, unsigned id)
{
	if (options->autodetect)
		return;

	SourceLocation loc = stmt->getLocStart();
	DiagnosticsEngine &diag = PP.getDiagnostics();
	DiagnosticBuilder B = diag.Report(loc, id) << stmt->getSourceRange();
}

/* Called if we found something we (currently) cannot handle.
 * We'll provide more informative warnings later.
 *
 * We only actually complain if autodetect is false.
 */
void PetScan::unsupported(Stmt *stmt)
{
	DiagnosticsEngine &diag = PP.getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "unsupported");
	report(stmt, id);
}

/* Report a missing prototype, unless autodetect is set.
 */
void PetScan::report_prototype_required(Stmt *stmt)
{
	DiagnosticsEngine &diag = PP.getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "prototype required");
	report(stmt, id);
}

/* Report a missing increment, unless autodetect is set.
 */
void PetScan::report_missing_increment(Stmt *stmt)
{
	DiagnosticsEngine &diag = PP.getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "missing increment");
	report(stmt, id);
}

/* Extract an integer from "expr".
 */
__isl_give isl_val *PetScan::extract_int(isl_ctx *ctx, IntegerLiteral *expr)
{
	const Type *type = expr->getType().getTypePtr();
	int is_signed = type->hasSignedIntegerRepresentation();
	llvm::APInt val = expr->getValue();
	int is_negative = is_signed && val.isNegative();
	isl_val *v;

	if (is_negative)
		val = -val;

	v = extract_unsigned(ctx, val);

	if (is_negative)
		v = isl_val_neg(v);
	return v;
}

/* Extract an integer from "val", which is assumed to be non-negative.
 */
__isl_give isl_val *PetScan::extract_unsigned(isl_ctx *ctx,
	const llvm::APInt &val)
{
	unsigned n;
	const uint64_t *data;

	data = val.getRawData();
	n = val.getNumWords();
	return isl_val_int_from_chunks(ctx, n, sizeof(uint64_t), data);
}

/* Extract an integer from "expr".
 * Return NULL if "expr" does not (obviously) represent an integer.
 */
__isl_give isl_val *PetScan::extract_int(clang::ParenExpr *expr)
{
	return extract_int(expr->getSubExpr());
}

/* Extract an integer from "expr".
 * Return NULL if "expr" does not (obviously) represent an integer.
 */
__isl_give isl_val *PetScan::extract_int(clang::Expr *expr)
{
	if (expr->getStmtClass() == Stmt::IntegerLiteralClass)
		return extract_int(ctx, cast<IntegerLiteral>(expr));
	if (expr->getStmtClass() == Stmt::ParenExprClass)
		return extract_int(cast<ParenExpr>(expr));

	unsupported(expr);
	return NULL;
}

/* Extract a pet_expr from the APInt "val", which is assumed
 * to be non-negative.
 */
__isl_give pet_expr *PetScan::extract_expr(const llvm::APInt &val)
{
	return pet_expr_new_int(extract_unsigned(ctx, val));
}

/* Return the number of bits needed to represent the type "qt",
 * if it is an integer type.  Otherwise return 0.
 * If qt is signed then return the opposite of the number of bits.
 */
static int get_type_size(QualType qt, ASTContext &ast_context)
{
	int size;

	if (!qt->isIntegerType())
		return 0;

	size = ast_context.getIntWidth(qt);
	if (!qt->isUnsignedIntegerType())
		size = -size;

	return size;
}

/* Return the number of bits needed to represent the type of "decl",
 * if it is an integer type.  Otherwise return 0.
 * If qt is signed then return the opposite of the number of bits.
 */
static int get_type_size(ValueDecl *decl)
{
	return get_type_size(decl->getType(), decl->getASTContext());
}

/* Bound parameter "pos" of "set" to the possible values of "decl".
 */
static __isl_give isl_set *set_parameter_bounds(__isl_take isl_set *set,
	unsigned pos, ValueDecl *decl)
{
	int type_size;
	isl_ctx *ctx;
	isl_val *bound;

	ctx = isl_set_get_ctx(set);
	type_size = get_type_size(decl);
	if (type_size == 0)
		isl_die(ctx, isl_error_invalid, "not an integer type",
			return isl_set_free(set));
	if (type_size > 0) {
		set = isl_set_lower_bound_si(set, isl_dim_param, pos, 0);
		bound = isl_val_int_from_ui(ctx, type_size);
		bound = isl_val_2exp(bound);
		bound = isl_val_sub_ui(bound, 1);
		set = isl_set_upper_bound_val(set, isl_dim_param, pos, bound);
	} else {
		bound = isl_val_int_from_ui(ctx, -type_size - 1);
		bound = isl_val_2exp(bound);
		bound = isl_val_sub_ui(bound, 1);
		set = isl_set_upper_bound_val(set, isl_dim_param, pos,
						isl_val_copy(bound));
		bound = isl_val_neg(bound);
		bound = isl_val_sub_ui(bound, 1);
		set = isl_set_lower_bound_val(set, isl_dim_param, pos, bound);
	}

	return set;
}

__isl_give pet_expr *PetScan::extract_index_expr(ImplicitCastExpr *expr)
{
	return extract_index_expr(expr->getSubExpr());
}

/* Return the depth of an array of the given type.
 */
static int array_depth(const Type *type)
{
	if (type->isPointerType())
		return 1 + array_depth(type->getPointeeType().getTypePtr());
	if (type->isArrayType()) {
		const ArrayType *atype;
		type = type->getCanonicalTypeInternal().getTypePtr();
		atype = cast<ArrayType>(type);
		return 1 + array_depth(atype->getElementType().getTypePtr());
	}
	return 0;
}

/* Return the depth of the array accessed by the index expression "index".
 * If "index" is an affine expression, i.e., if it does not access
 * any array, then return 1.
 * If "index" represent a member access, i.e., if its range is a wrapped
 * relation, then return the sum of the depth of the array of structures
 * and that of the member inside the structure.
 */
static int extract_depth(__isl_keep isl_multi_pw_aff *index)
{
	isl_id *id;
	ValueDecl *decl;

	if (!index)
		return -1;

	if (isl_multi_pw_aff_range_is_wrapping(index)) {
		int domain_depth, range_depth;
		isl_multi_pw_aff *domain, *range;

		domain = isl_multi_pw_aff_copy(index);
		domain = isl_multi_pw_aff_range_factor_domain(domain);
		domain_depth = extract_depth(domain);
		isl_multi_pw_aff_free(domain);
		range = isl_multi_pw_aff_copy(index);
		range = isl_multi_pw_aff_range_factor_range(range);
		range_depth = extract_depth(range);
		isl_multi_pw_aff_free(range);

		return domain_depth + range_depth;
	}

	if (!isl_multi_pw_aff_has_tuple_id(index, isl_dim_out))
		return 1;

	id = isl_multi_pw_aff_get_tuple_id(index, isl_dim_out);
	if (!id)
		return -1;
	decl = (ValueDecl *) isl_id_get_user(id);
	isl_id_free(id);

	return array_depth(decl->getType().getTypePtr());
}

/* Return the depth of the array accessed by the access expression "expr".
 */
static int extract_depth(__isl_keep pet_expr *expr)
{
	isl_multi_pw_aff *index;
	int depth;

	index = pet_expr_access_get_index(expr);
	depth = extract_depth(index);
	isl_multi_pw_aff_free(index);

	return depth;
}

/* Construct a pet_expr representing an index expression for an access
 * to the variable referenced by "expr".
 */
__isl_give pet_expr *PetScan::extract_index_expr(DeclRefExpr *expr)
{
	return extract_index_expr(expr->getDecl());
}

/* Construct a pet_expr representing an index expression for an access
 * to the variable "decl".
 */
__isl_give pet_expr *PetScan::extract_index_expr(ValueDecl *decl)
{
	isl_id *id = create_decl_id(ctx, decl);
	isl_space *space = isl_space_alloc(ctx, 0, 0, 0);

	space = isl_space_set_tuple_id(space, isl_dim_out, id);

	return pet_expr_from_index(isl_multi_pw_aff_zero(space));
}

/* Construct a pet_expr representing the index expression "expr"
 * Return NULL on error.
 */
__isl_give pet_expr *PetScan::extract_index_expr(Expr *expr)
{
	switch (expr->getStmtClass()) {
	case Stmt::ImplicitCastExprClass:
		return extract_index_expr(cast<ImplicitCastExpr>(expr));
	case Stmt::DeclRefExprClass:
		return extract_index_expr(cast<DeclRefExpr>(expr));
	case Stmt::ArraySubscriptExprClass:
		return extract_index_expr(cast<ArraySubscriptExpr>(expr));
	case Stmt::IntegerLiteralClass:
		return extract_expr(cast<IntegerLiteral>(expr));
	case Stmt::MemberExprClass:
		return extract_index_expr(cast<MemberExpr>(expr));
	default:
		unsupported(expr);
	}
	return NULL;
}

/* Extract an index expression from the given array subscript expression.
 *
 * We first extract an index expression from the base.
 * This will result in an index expression with a range that corresponds
 * to the earlier indices.
 * We then extract the current index and let
 * pet_expr_access_subscript combine the two.
 */
__isl_give pet_expr *PetScan::extract_index_expr(ArraySubscriptExpr *expr)
{
	Expr *base = expr->getBase();
	Expr *idx = expr->getIdx();
	pet_expr *index;
	pet_expr *base_expr;

	base_expr = extract_index_expr(base);
	index = extract_expr(idx);

	base_expr = pet_expr_access_subscript(base_expr, index);

	return base_expr;
}

/* Extract an index expression from a member expression.
 *
 * If the base access (to the structure containing the member)
 * is of the form
 *
 *	A[..]
 *
 * and the member is called "f", then the member access is of
 * the form
 *
 *	A_f[A[..] -> f[]]
 *
 * If the member access is to an anonymous struct, then simply return
 *
 *	A[..]
 *
 * If the member access in the source code is of the form
 *
 *	A->f
 *
 * then it is treated as
 *
 *	A[0].f
 */
__isl_give pet_expr *PetScan::extract_index_expr(MemberExpr *expr)
{
	Expr *base = expr->getBase();
	FieldDecl *field = cast<FieldDecl>(expr->getMemberDecl());
	pet_expr *base_index;
	isl_id *id;

	base_index = extract_index_expr(base);

	if (expr->isArrow()) {
		pet_expr *index = pet_expr_new_int(isl_val_zero(ctx));
		base_index = pet_expr_access_subscript(base_index, index);
	}

	if (field->isAnonymousStructOrUnion())
		return base_index;

	id = create_decl_id(ctx, field);

	return pet_expr_access_member(base_index, id);
}

/* Mark the given access pet_expr as a write.
 */
static __isl_give pet_expr *mark_write(__isl_take pet_expr *access)
{
	access = pet_expr_access_set_write(access, 1);
	access = pet_expr_access_set_read(access, 0);

	return access;
}

/* Construct a pet_expr representing a unary operator expression.
 */
__isl_give pet_expr *PetScan::extract_expr(UnaryOperator *expr)
{
	pet_expr *arg;
	enum pet_op_type op;

	op = UnaryOperatorKind2pet_op_type(expr->getOpcode());
	if (op == pet_op_last) {
		unsupported(expr);
		return NULL;
	}

	arg = extract_expr(expr->getSubExpr());

	if (expr->isIncrementDecrementOp() &&
	    pet_expr_get_type(arg) == pet_expr_access) {
		arg = mark_write(arg);
		arg = pet_expr_access_set_read(arg, 1);
	}

	return pet_expr_new_unary(op, arg);
}

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
	if (!scop)
		return pet_context_free(pc);
	for (int i = 0; i < scop->n_stmt; ++i)
		pc = handle_writes(scop->stmts[i], pc);

	return pc;
}

/* Construct a pet_expr representing a binary operator expression.
 *
 * If the top level operator is an assignment and the LHS is an access,
 * then we mark that access as a write.  If the operator is a compound
 * assignment, the access is marked as both a read and a write.
 */
__isl_give pet_expr *PetScan::extract_expr(BinaryOperator *expr)
{
	int type_size;
	pet_expr *lhs, *rhs;
	enum pet_op_type op;

	op = BinaryOperatorKind2pet_op_type(expr->getOpcode());
	if (op == pet_op_last) {
		unsupported(expr);
		return NULL;
	}

	lhs = extract_expr(expr->getLHS());
	rhs = extract_expr(expr->getRHS());

	if (expr->isAssignmentOp() &&
	    pet_expr_get_type(lhs) == pet_expr_access) {
		lhs = mark_write(lhs);
		if (expr->isCompoundAssignmentOp())
			lhs = pet_expr_access_set_read(lhs, 1);
	}

	type_size = get_type_size(expr->getType(), ast_context);
	return pet_expr_new_binary(type_size, op, lhs, rhs);
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

/* Construct a pet_tree for a (single) variable declaration.
 */
__isl_give pet_tree *PetScan::extract(DeclStmt *stmt)
{
	Decl *decl;
	VarDecl *vd;
	pet_expr *lhs, *rhs;
	pet_tree *tree;

	if (!stmt->isSingleDecl()) {
		unsupported(stmt);
		return NULL;
	}

	decl = stmt->getSingleDecl();
	vd = cast<VarDecl>(decl);

	lhs = extract_access_expr(vd);
	lhs = mark_write(lhs);
	if (!vd->getInit())
		tree = pet_tree_new_decl(lhs);
	else {
		rhs = extract_expr(vd->getInit());
		tree = pet_tree_new_decl_init(lhs, rhs);
	}

	return tree;
}

/* Construct a pet_expr representing a conditional operation.
 */
__isl_give pet_expr *PetScan::extract_expr(ConditionalOperator *expr)
{
	pet_expr *cond, *lhs, *rhs;
	isl_pw_aff *pa;

	cond = extract_expr(expr->getCond());
	lhs = extract_expr(expr->getTrueExpr());
	rhs = extract_expr(expr->getFalseExpr());

	return pet_expr_new_ternary(cond, lhs, rhs);
}

__isl_give pet_expr *PetScan::extract_expr(ImplicitCastExpr *expr)
{
	return extract_expr(expr->getSubExpr());
}

/* Construct a pet_expr representing a floating point value.
 *
 * If the floating point literal does not appear in a macro,
 * then we use the original representation in the source code
 * as the string representation.  Otherwise, we use the pretty
 * printer to produce a string representation.
 */
__isl_give pet_expr *PetScan::extract_expr(FloatingLiteral *expr)
{
	double d;
	string s;
	const LangOptions &LO = PP.getLangOpts();
	SourceLocation loc = expr->getLocation();

	if (!loc.isMacroID()) {
		SourceManager &SM = PP.getSourceManager();
		unsigned len = Lexer::MeasureTokenLength(loc, SM, LO);
		s = string(SM.getCharacterData(loc), len);
	} else {
		llvm::raw_string_ostream S(s);
		expr->printPretty(S, 0, PrintingPolicy(LO));
		S.str();
	}
	d = expr->getValueAsApproximateDouble();
	return pet_expr_new_double(ctx, d, s.c_str());
}

/* Convert the index expression "index" into an access pet_expr of type "qt".
 */
__isl_give pet_expr *PetScan::extract_access_expr(QualType qt,
	__isl_take pet_expr *index)
{
	int depth;
	int type_size;

	depth = extract_depth(index);
	type_size = get_type_size(qt, ast_context);

	index = pet_expr_set_type_size(index, type_size);
	index = pet_expr_access_set_depth(index, depth);

	return index;
}

/* Extract an index expression from "expr" and then convert it into
 * an access pet_expr.
 */
__isl_give pet_expr *PetScan::extract_access_expr(Expr *expr)
{
	return extract_access_expr(expr->getType(), extract_index_expr(expr));
}

/* Extract an index expression from "decl" and then convert it into
 * an access pet_expr.
 */
__isl_give pet_expr *PetScan::extract_access_expr(ValueDecl *decl)
{
	return extract_access_expr(decl->getType(), extract_index_expr(decl));
}

__isl_give pet_expr *PetScan::extract_expr(ParenExpr *expr)
{
	return extract_expr(expr->getSubExpr());
}

/* Extract an assume statement from the argument "expr"
 * of a __pencil_assume statement.
 */
__isl_give pet_expr *PetScan::extract_assume(Expr *expr)
{
	return pet_expr_new_unary(pet_op_assume, extract_expr(expr));
}

/* Construct a pet_expr corresponding to the function call argument "expr".
 * The argument appears in position "pos" of a call to function "fd".
 *
 * If we are passing along a pointer to an array element
 * or an entire row or even higher dimensional slice of an array,
 * then the function being called may write into the array.
 *
 * We assume here that if the function is declared to take a pointer
 * to a const type, then the function will perform a read
 * and that otherwise, it will perform a write.
 */
__isl_give pet_expr *PetScan::extract_argument(FunctionDecl *fd, int pos,
	Expr *expr)
{
	pet_expr *res;
	int is_addr = 0, is_partial = 0;
	Stmt::StmtClass sc;

	if (expr->getStmtClass() == Stmt::ImplicitCastExprClass) {
		ImplicitCastExpr *ice = cast<ImplicitCastExpr>(expr);
		expr = ice->getSubExpr();
	}
	if (expr->getStmtClass() == Stmt::UnaryOperatorClass) {
		UnaryOperator *op = cast<UnaryOperator>(expr);
		if (op->getOpcode() == UO_AddrOf) {
			is_addr = 1;
			expr = op->getSubExpr();
		}
	}
	res = extract_expr(expr);
	if (!res)
		return NULL;
	sc = expr->getStmtClass();
	if ((sc == Stmt::ArraySubscriptExprClass ||
	     sc == Stmt::MemberExprClass) &&
	    array_depth(expr->getType().getTypePtr()) > 0)
		is_partial = 1;
	if ((is_addr || is_partial) &&
	    pet_expr_get_type(res) == pet_expr_access) {
		ParmVarDecl *parm;
		if (!fd->hasPrototype()) {
			report_prototype_required(expr);
			return pet_expr_free(res);
		}
		parm = fd->getParamDecl(pos);
		if (!const_base(parm->getType()))
			res = mark_write(res);
	}

	if (is_addr)
		res = pet_expr_new_unary(pet_op_address_of, res);
	return res;
}

/* Construct a pet_expr representing a function call.
 *
 * In the special case of a "call" to __pencil_assume,
 * construct an assume expression instead.
 */
__isl_give pet_expr *PetScan::extract_expr(CallExpr *expr)
{
	pet_expr *res = NULL;
	FunctionDecl *fd;
	string name;
	unsigned n_arg;

	fd = expr->getDirectCallee();
	if (!fd) {
		unsupported(expr);
		return NULL;
	}

	name = fd->getDeclName().getAsString();
	n_arg = expr->getNumArgs();

	if (n_arg == 1 && name == "__pencil_assume")
		return extract_assume(expr->getArg(0));

	res = pet_expr_new_call(ctx, name.c_str(), n_arg);
	if (!res)
		return NULL;

	for (int i = 0; i < n_arg; ++i) {
		Expr *arg = expr->getArg(i);
		res = pet_expr_set_arg(res, i,
					PetScan::extract_argument(fd, i, arg));
	}

	return res;
}

/* Construct a pet_expr representing a (C style) cast.
 */
__isl_give pet_expr *PetScan::extract_expr(CStyleCastExpr *expr)
{
	pet_expr *arg;
	QualType type;

	arg = extract_expr(expr->getSubExpr());
	if (!arg)
		return NULL;

	type = expr->getTypeAsWritten();
	return pet_expr_new_cast(type.getAsString().c_str(), arg);
}

/* Construct a pet_expr representing an integer.
 */
__isl_give pet_expr *PetScan::extract_expr(IntegerLiteral *expr)
{
	return pet_expr_new_int(extract_int(expr));
}

/* Try and construct a pet_expr representing "expr".
 */
__isl_give pet_expr *PetScan::extract_expr(Expr *expr)
{
	switch (expr->getStmtClass()) {
	case Stmt::UnaryOperatorClass:
		return extract_expr(cast<UnaryOperator>(expr));
	case Stmt::CompoundAssignOperatorClass:
	case Stmt::BinaryOperatorClass:
		return extract_expr(cast<BinaryOperator>(expr));
	case Stmt::ImplicitCastExprClass:
		return extract_expr(cast<ImplicitCastExpr>(expr));
	case Stmt::ArraySubscriptExprClass:
	case Stmt::DeclRefExprClass:
	case Stmt::MemberExprClass:
		return extract_access_expr(expr);
	case Stmt::IntegerLiteralClass:
		return extract_expr(cast<IntegerLiteral>(expr));
	case Stmt::FloatingLiteralClass:
		return extract_expr(cast<FloatingLiteral>(expr));
	case Stmt::ParenExprClass:
		return extract_expr(cast<ParenExpr>(expr));
	case Stmt::ConditionalOperatorClass:
		return extract_expr(cast<ConditionalOperator>(expr));
	case Stmt::CallExprClass:
		return extract_expr(cast<CallExpr>(expr));
	case Stmt::CStyleCastExprClass:
		return extract_expr(cast<CStyleCastExpr>(expr));
	default:
		unsupported(expr);
	}
	return NULL;
}

/* Check if the given initialization statement is an assignment.
 * If so, return that assignment.  Otherwise return NULL.
 */
BinaryOperator *PetScan::initialization_assignment(Stmt *init)
{
	BinaryOperator *ass;

	if (init->getStmtClass() != Stmt::BinaryOperatorClass)
		return NULL;

	ass = cast<BinaryOperator>(init);
	if (ass->getOpcode() != BO_Assign)
		return NULL;

	return ass;
}

/* Check if the given initialization statement is a declaration
 * of a single variable.
 * If so, return that declaration.  Otherwise return NULL.
 */
Decl *PetScan::initialization_declaration(Stmt *init)
{
	DeclStmt *decl;

	if (init->getStmtClass() != Stmt::DeclStmtClass)
		return NULL;

	decl = cast<DeclStmt>(init);

	if (!decl->isSingleDecl())
		return NULL;

	return decl->getSingleDecl();
}

/* Given the assignment operator in the initialization of a for loop,
 * extract the induction variable, i.e., the (integer)variable being
 * assigned.
 */
ValueDecl *PetScan::extract_induction_variable(BinaryOperator *init)
{
	Expr *lhs;
	DeclRefExpr *ref;
	ValueDecl *decl;
	const Type *type;

	lhs = init->getLHS();
	if (lhs->getStmtClass() != Stmt::DeclRefExprClass) {
		unsupported(init);
		return NULL;
	}

	ref = cast<DeclRefExpr>(lhs);
	decl = ref->getDecl();
	type = decl->getType().getTypePtr();

	if (!type->isIntegerType()) {
		unsupported(lhs);
		return NULL;
	}

	return decl;
}

/* Given the initialization statement of a for loop and the single
 * declaration in this initialization statement,
 * extract the induction variable, i.e., the (integer) variable being
 * declared.
 */
VarDecl *PetScan::extract_induction_variable(Stmt *init, Decl *decl)
{
	VarDecl *vd;

	vd = cast<VarDecl>(decl);

	const QualType type = vd->getType();
	if (!type->isIntegerType()) {
		unsupported(init);
		return NULL;
	}

	if (!vd->getInit()) {
		unsupported(init);
		return NULL;
	}

	return vd;
}

/* Check that op is of the form iv++ or iv--.
 * Return a pet_expr representing "1" or "-1" accordingly.
 */
__isl_give pet_expr *PetScan::extract_unary_increment(
	clang::UnaryOperator *op, clang::ValueDecl *iv)
{
	Expr *sub;
	DeclRefExpr *ref;
	isl_val *v;

	if (!op->isIncrementDecrementOp()) {
		unsupported(op);
		return NULL;
	}

	sub = op->getSubExpr();
	if (sub->getStmtClass() != Stmt::DeclRefExprClass) {
		unsupported(op);
		return NULL;
	}

	ref = cast<DeclRefExpr>(sub);
	if (ref->getDecl() != iv) {
		unsupported(op);
		return NULL;
	}

	if (op->isIncrementOp())
		v = isl_val_one(ctx);
	else
		v = isl_val_negone(ctx);

	return pet_expr_new_int(v);
}

/* Check if op is of the form
 *
 *	iv = expr
 *
 * and return the increment "expr - iv" as a pet_expr.
 */
__isl_give pet_expr *PetScan::extract_binary_increment(BinaryOperator *op,
	clang::ValueDecl *iv)
{
	int type_size;
	Expr *lhs;
	DeclRefExpr *ref;
	pet_expr *expr, *expr_iv;

	if (op->getOpcode() != BO_Assign) {
		unsupported(op);
		return NULL;
	}

	lhs = op->getLHS();
	if (lhs->getStmtClass() != Stmt::DeclRefExprClass) {
		unsupported(op);
		return NULL;
	}

	ref = cast<DeclRefExpr>(lhs);
	if (ref->getDecl() != iv) {
		unsupported(op);
		return NULL;
	}

	expr = extract_expr(op->getRHS());
	expr_iv = extract_expr(lhs);

	type_size = get_type_size(iv->getType(), ast_context);
	return pet_expr_new_binary(type_size, pet_op_sub, expr, expr_iv);
}

/* Check that op is of the form iv += cst or iv -= cst
 * and return a pet_expr corresponding to cst or -cst accordingly.
 */
__isl_give pet_expr *PetScan::extract_compound_increment(
	CompoundAssignOperator *op, clang::ValueDecl *iv)
{
	Expr *lhs;
	DeclRefExpr *ref;
	bool neg = false;
	pet_expr *expr;
	BinaryOperatorKind opcode;

	opcode = op->getOpcode();
	if (opcode != BO_AddAssign && opcode != BO_SubAssign) {
		unsupported(op);
		return NULL;
	}
	if (opcode == BO_SubAssign)
		neg = true;

	lhs = op->getLHS();
	if (lhs->getStmtClass() != Stmt::DeclRefExprClass) {
		unsupported(op);
		return NULL;
	}

	ref = cast<DeclRefExpr>(lhs);
	if (ref->getDecl() != iv) {
		unsupported(op);
		return NULL;
	}

	expr = extract_expr(op->getRHS());
	if (neg)
		expr = pet_expr_new_unary(pet_op_minus, expr);

	return expr;
}

/* Check that the increment of the given for loop increments
 * (or decrements) the induction variable "iv" and return
 * the increment as a pet_expr if successful.
 */
__isl_give pet_expr *PetScan::extract_increment(clang::ForStmt *stmt,
	ValueDecl *iv)
{
	Stmt *inc = stmt->getInc();

	if (!inc) {
		report_missing_increment(stmt);
		return NULL;
	}

	if (inc->getStmtClass() == Stmt::UnaryOperatorClass)
		return extract_unary_increment(cast<UnaryOperator>(inc), iv);
	if (inc->getStmtClass() == Stmt::CompoundAssignOperatorClass)
		return extract_compound_increment(
				cast<CompoundAssignOperator>(inc), iv);
	if (inc->getStmtClass() == Stmt::BinaryOperatorClass)
		return extract_binary_increment(cast<BinaryOperator>(inc), iv);

	unsupported(inc);
	return NULL;
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

/* Create the infinite iteration domain
 *
 *	{ [id] : id >= 0 }
 *
 * If "scop" has an affine skip of type pet_skip_later,
 * then remove those iterations i that have an earlier iteration
 * where the skip condition is satisfied, meaning that iteration i
 * is not executed.
 * Since we are dealing with a loop without loop iterator,
 * the skip condition cannot refer to the current loop iterator and
 * so effectively, the returned set is of the form
 *
 *	{ [0]; [id] : id >= 1 and not skip }
 */
static __isl_give isl_set *infinite_domain(__isl_take isl_id *id,
	struct pet_scop *scop)
{
	isl_ctx *ctx = isl_id_get_ctx(id);
	isl_set *domain;
	isl_set *skip;

	domain = isl_set_nat_universe(isl_space_set_alloc(ctx, 0, 1));
	domain = isl_set_set_dim_id(domain, isl_dim_set, 0, id);

	if (!pet_scop_has_affine_skip(scop, pet_skip_later))
		return domain;

	skip = pet_scop_get_affine_skip_domain(scop, pet_skip_later);
	skip = embed(skip, isl_id_copy(id));
	skip = isl_set_intersect(skip , isl_set_copy(domain));
	domain = isl_set_subtract(domain, after(skip, 1));

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
 * account in infinite_domain (if the skip condition is affine)
 * or in scop_add_break (if the skip condition is not affine).
 */
static struct pet_scop *scop_from_infinite_loop(__isl_keep pet_tree *body,
	__isl_keep pet_context *pc, struct pet_state *state)
{
	isl_ctx *ctx;
	isl_id *id, *id_test;
	isl_set *domain;
	isl_aff *ident;
	struct pet_scop *scop;
	bool has_var_break;

	scop = scop_from_tree(body, pc, state);

	ctx = pet_tree_get_ctx(body);
	id = isl_id_alloc(ctx, "t", NULL);
	domain = infinite_domain(isl_id_copy(id), scop);
	ident = identity_aff(domain);

	has_var_break = pet_scop_has_var_skip(scop, pet_skip_later);
	if (has_var_break)
		id_test = pet_scop_get_skip_id(scop, pet_skip_later);

	scop = pet_scop_embed(scop, isl_set_copy(domain),
				isl_aff_copy(ident), ident, id);
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
 * account in infinite_domain (if the skip condition is affine)
 * or in scop_add_break (if the skip condition is not affine).
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
	isl_aff *ident;
	struct pet_scop *scop;
	bool has_var_break;

	ctx = state->ctx;
	test_index = pet_create_test_index(ctx, test_nr);
	scop = scop_from_non_affine_condition(cond, stmt_nr,
				isl_multi_pw_aff_copy(test_index), loc, pc);
	id_test = isl_multi_pw_aff_get_tuple_id(test_index, isl_dim_out);
	scop = pet_scop_add_boolean_array(scop, test_index, state->int_size);

	id = isl_id_alloc(ctx, "t", NULL);
	domain = infinite_domain(isl_id_copy(id), scop_body);
	ident = identity_aff(domain);

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

/* Construct a pet_tree for a while loop.
 *
 * If we were only able to extract part of the body, then simply
 * return that part.
 */
__isl_give pet_tree *PetScan::extract(WhileStmt *stmt)
{
	pet_expr *pe_cond;
	pet_tree *tree;

	tree = extract(stmt->getBody());
	if (partial)
		return tree;
	pe_cond = extract_expr(stmt->getCond());
	tree = pet_tree_new_while(pe_cond, tree);

	return tree;
}

/* Check whether "cond" expresses a simple loop bound
 * on the only set dimension.
 * In particular, if "up" is set then "cond" should contain only
 * upper bounds on the set dimension.
 * Otherwise, it should contain only lower bounds.
 */
static bool is_simple_bound(__isl_keep isl_set *cond, __isl_keep isl_val *inc)
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
static bool can_wrap(__isl_keep isl_set *cond, __isl_keep pet_expr *iv,
	__isl_keep isl_val *inc)
{
	bool cw;
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
 * "expr" assigned anywhere inside "scop"?
 */
static bool is_assigned(__isl_keep pet_expr *expr, pet_scop *scop)
{
	bool assigned = false;
	isl_id *id;

	id = pet_expr_access_get_id(expr);
	assigned = pet_scop_writes(scop, id);
	isl_id_free(id);

	return assigned;
}

/* Are all nested access parameters in "pa" allowed given "scop".
 * In particular, is none of them written by anywhere inside "scop".
 *
 * If "scop" has any skip conditions, then no nested access parameters
 * are allowed.  In particular, if there is any nested access in a guard
 * for a piece of code containing a "continue", then we want to introduce
 * a separate statement for evaluating this guard so that we can express
 * that the result is false for all previous iterations.
 */
static bool is_nested_allowed(__isl_keep isl_pw_aff *pa, struct pet_scop *scop)
{
	int nparam;

	if (!scop)
		return true;

	if (!pet_nested_any_in_pw_aff(pa))
		return true;

	if (pet_scop_has_skip(scop, pet_skip_now))
		return false;

	nparam = isl_pw_aff_dim(pa, isl_dim_param);
	for (int i = 0; i < nparam; ++i) {
		isl_id *id = isl_pw_aff_get_dim_id(pa, isl_dim_param, i);
		pet_expr *expr;
		bool allowed;

		if (!pet_nested_in_id(id)) {
			isl_id_free(id);
			continue;
		}

		expr = pet_nested_extract_expr(id);
		allowed = pet_expr_get_type(expr) == pet_expr_access &&
			    !is_assigned(expr, scop);

		pet_expr_free(expr);
		isl_id_free(id);

		if (!allowed)
			return false;
	}

	return true;
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
	bool is_one;
	bool is_unsigned;
	bool is_simple;
	bool is_virtual;
	bool has_affine_break;
	bool has_var_break;
	isl_aff *wrap = NULL;
	isl_pw_aff *pa;
	isl_set *valid_init;
	isl_set *valid_cond;
	isl_set *valid_cond_init;
	isl_set *valid_cond_next;
	isl_set *valid_inc;
	int stmt_id;
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
	if (isl_pw_aff_involves_nan(pa) || pet_nested_any_in_pw_aff(pa))
		stmt_id = state->n_stmt++;

	scop = scop_from_tree(tree->u.l.body, pc, state);

	valid_inc = isl_pw_aff_domain(pa_inc);

	is_unsigned = pet_expr_get_type_size(tree->u.l.iv) > 0;

	has_affine_break = scop &&
				pet_scop_has_affine_skip(scop, pet_skip_later);
	if (has_affine_break)
		skip = pet_scop_get_affine_skip_domain(scop, pet_skip_later);
	has_var_break = scop && pet_scop_has_var_skip(scop, pet_skip_later);
	if (has_var_break)
		id_break_test = pet_scop_get_skip_id(scop, pet_skip_later);

	if (isl_pw_aff_involves_nan(pa) || !is_nested_allowed(pa, scop))
		pa = isl_pw_aff_free(pa);

	valid_cond = isl_pw_aff_domain(isl_pw_aff_copy(pa));
	cond = isl_pw_aff_non_zero_set(pa);
	if (!cond) {
		isl_multi_pw_aff *test_index;
		int save_n_stmt = state->n_stmt;
		test_index = pet_create_test_index(state->ctx, state->n_test++);
		state->n_stmt = stmt_id;
		scop_cond = scop_from_non_affine_condition(
				pet_expr_copy(tree->u.l.cond), state->n_stmt++,
				isl_multi_pw_aff_copy(test_index),
				pet_tree_get_loc(tree), pc);
		state->n_stmt = save_n_stmt;
		id_test = isl_multi_pw_aff_get_tuple_id(test_index,
							isl_dim_out);
		scop_cond = pet_scop_add_boolean_array(scop_cond, test_index,
				state->int_size);
		scop_cond = pet_scop_prefix(scop_cond, 0);
		scop = pet_scop_reset_context(scop);
		scop = pet_scop_prefix(scop, 1);
		cond = isl_set_universe(isl_space_set_alloc(state->ctx, 0, 0));
	}

	cond = embed(cond, isl_id_copy(id));
	skip = embed(skip, isl_id_copy(id));
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
		isl_map *rev_wrap;
		wrap = compute_wrapping(isl_set_get_space(cond), tree->u.l.iv);
		rev_wrap = isl_map_from_aff(isl_aff_copy(wrap));
		rev_wrap = isl_map_reverse(rev_wrap);
		cond = isl_set_apply(cond, isl_map_copy(rev_wrap));
		skip = isl_set_apply(skip, isl_map_copy(rev_wrap));
		valid_cond = isl_set_apply(valid_cond, isl_map_copy(rev_wrap));
		valid_inc = isl_set_apply(valid_inc, rev_wrap);
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
	if (has_affine_break) {
		skip = isl_set_intersect(skip , isl_set_copy(domain));
		skip = after(skip, isl_val_sgn(inc));
		domain = isl_set_subtract(domain, skip);
	}
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

	scop_cond = pet_scop_embed(scop_cond, isl_set_copy(domain),
		    isl_aff_copy(sched), isl_aff_copy(wrap), isl_id_copy(id));
	scop = pet_scop_embed(scop, isl_set_copy(domain), sched, wrap, id);
	scop = pet_scop_resolve_nested(scop);
	if (has_var_break)
		scop = scop_add_break(scop, id_break_test, isl_set_copy(domain),
					isl_val_copy(inc));
	if (id_test) {
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

/* Construct a pet_tree for a for statement.
 * The for loop is required to be of one of the following forms
 *
 *	for (i = init; condition; ++i)
 *	for (i = init; condition; --i)
 *	for (i = init; condition; i += constant)
 *	for (i = init; condition; i -= constant)
 *
 * We extract a pet_tree for the body and then include it in a pet_tree
 * of type pet_tree_for.
 *
 * As a special case, we also allow a for loop of the form
 *
 *	for (;;)
 *
 * in which case we return a pet_tree of type pet_tree_infinite_loop.
 *
 * If we were only able to extract part of the body, then simply
 * return that part.
 */
__isl_give pet_tree *PetScan::extract_for(ForStmt *stmt)
{
	BinaryOperator *ass;
	Decl *decl;
	Stmt *init;
	Expr *lhs, *rhs;
	ValueDecl *iv;
	pet_tree *tree;
	struct pet_scop *scop;
	int declared;
	pet_expr *pe_init, *pe_inc, *pe_iv, *pe_cond;

	if (!stmt->getInit() && !stmt->getCond() && !stmt->getInc()) {
		tree = extract(stmt->getBody());
		if (partial)
			return tree;
		tree = pet_tree_new_infinite_loop(tree);
		return tree;
	}

	init = stmt->getInit();
	if (!init) {
		unsupported(stmt);
		return NULL;
	}
	if ((ass = initialization_assignment(init)) != NULL) {
		iv = extract_induction_variable(ass);
		if (!iv)
			return NULL;
		lhs = ass->getLHS();
		rhs = ass->getRHS();
	} else if ((decl = initialization_declaration(init)) != NULL) {
		VarDecl *var = extract_induction_variable(init, decl);
		if (!var)
			return NULL;
		iv = var;
		rhs = var->getInit();
		lhs = create_DeclRefExpr(var);
	} else {
		unsupported(stmt->getInit());
		return NULL;
	}

	declared = !initialization_assignment(stmt->getInit());
	tree = extract(stmt->getBody());
	if (partial)
		return tree;
	pe_iv = extract_access_expr(iv);
	pe_iv = mark_write(pe_iv);
	pe_init = extract_expr(rhs);
	if (!stmt->getCond())
		pe_cond = pet_expr_new_int(isl_val_one(ctx));
	else
		pe_cond = extract_expr(stmt->getCond());
	pe_inc = extract_increment(stmt, iv);
	tree = pet_tree_new_for(declared, pe_iv, pe_init, pe_cond,
				pe_inc, tree);
	return tree;
}

/* Try and construct a pet_tree corresponding to a compound statement.
 *
 * "skip_declarations" is set if we should skip initial declarations
 * in the children of the compound statements.  This then implies
 * that this sequence of children should not be treated as a block
 * since the initial statements may be skipped.
 */
__isl_give pet_tree *PetScan::extract(CompoundStmt *stmt,
	bool skip_declarations)
{
	return extract(stmt->children(), !skip_declarations, skip_declarations);
}

/* Return the file offset of the expansion location of "Loc".
 */
static unsigned getExpansionOffset(SourceManager &SM, SourceLocation Loc)
{
	return SM.getFileOffset(SM.getExpansionLoc(Loc));
}

#ifdef HAVE_FINDLOCATIONAFTERTOKEN

/* Return a SourceLocation for the location after the first semicolon
 * after "loc".  If Lexer::findLocationAfterToken is available, we simply
 * call it and also skip trailing spaces and newline.
 */
static SourceLocation location_after_semi(SourceLocation loc, SourceManager &SM,
	const LangOptions &LO)
{
	return Lexer::findLocationAfterToken(loc, tok::semi, SM, LO, true);
}

#else

/* Return a SourceLocation for the location after the first semicolon
 * after "loc".  If Lexer::findLocationAfterToken is not available,
 * we look in the underlying character data for the first semicolon.
 */
static SourceLocation location_after_semi(SourceLocation loc, SourceManager &SM,
	const LangOptions &LO)
{
	const char *semi;
	const char *s = SM.getCharacterData(loc);

	semi = strchr(s, ';');
	if (!semi)
		return SourceLocation();
	return loc.getFileLocWithOffset(semi + 1 - s);
}

#endif

/* If the token at "loc" is the first token on the line, then return
 * a location referring to the start of the line.
 * Otherwise, return "loc".
 *
 * This function is used to extend a scop to the start of the line
 * if the first token of the scop is also the first token on the line.
 *
 * We look for the first token on the line.  If its location is equal to "loc",
 * then the latter is the location of the first token on the line.
 */
static SourceLocation move_to_start_of_line_if_first_token(SourceLocation loc,
	SourceManager &SM, const LangOptions &LO)
{
	std::pair<FileID, unsigned> file_offset_pair;
	llvm::StringRef file;
	const char *pos;
	Token tok;
	SourceLocation token_loc, line_loc;
	int col;

	loc = SM.getExpansionLoc(loc);
	col = SM.getExpansionColumnNumber(loc);
	line_loc = loc.getLocWithOffset(1 - col);
	file_offset_pair = SM.getDecomposedLoc(line_loc);
	file = SM.getBufferData(file_offset_pair.first, NULL);
	pos = file.data() + file_offset_pair.second;

	Lexer lexer(SM.getLocForStartOfFile(file_offset_pair.first), LO,
					file.begin(), pos, file.end());
	lexer.LexFromRawLexer(tok);
	token_loc = tok.getLocation();

	if (token_loc == loc)
		return line_loc;
	else
		return loc;
}

/* Construct a pet_loc corresponding to the region covered by "range".
 * If "skip_semi" is set, then we assume "range" is followed by
 * a semicolon and also include this semicolon.
 */
__isl_give pet_loc *PetScan::construct_pet_loc(SourceRange range,
	bool skip_semi)
{
	SourceLocation loc = range.getBegin();
	SourceManager &SM = PP.getSourceManager();
	const LangOptions &LO = PP.getLangOpts();
	int line = PP.getSourceManager().getExpansionLineNumber(loc);
	unsigned start, end;

	loc = move_to_start_of_line_if_first_token(loc, SM, LO);
	start = getExpansionOffset(SM, loc);
	loc = range.getEnd();
	if (skip_semi)
		loc = location_after_semi(loc, SM, LO);
	else
		loc = PP.getLocForEndOfToken(loc);
	end = getExpansionOffset(SM, loc);

	return pet_loc_alloc(ctx, start, end, line);
}

/* Convert a top-level pet_expr to an expression pet_tree.
 */
__isl_give pet_tree *PetScan::extract(__isl_take pet_expr *expr,
	SourceRange range, bool skip_semi)
{
	pet_loc *loc;
	pet_tree *tree;

	tree = pet_tree_new_expr(expr);
	loc = construct_pet_loc(range, skip_semi);
	tree = pet_tree_set_loc(tree, loc);

	return tree;
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
	pet_skip_info_if_extract_index(&skip, test_index, state->int_size,
					&state->n_stmt, &state->n_test);

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
	pet_skip_info_if_extract_cond(&skip, cond,
			    state->int_size, &state->n_stmt, &state->n_test);

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

/* Construct a pet_tree for an if statement.
 */
__isl_give pet_tree *PetScan::extract(IfStmt *stmt)
{
	pet_expr *pe_cond;
	pet_tree *tree, *tree_else;
	struct pet_scop *scop;
	int int_size;

	pe_cond = extract_expr(stmt->getCond());
	tree = extract(stmt->getThen());
	if (stmt->getElse()) {
		tree_else = extract(stmt->getElse());
		if (options->autodetect) {
			if (tree && !tree_else) {
				partial = true;
				pet_expr_free(pe_cond);
				return tree;
			}
			if (!tree && tree_else) {
				partial = true;
				pet_expr_free(pe_cond);
				return tree_else;
			}
		}
		tree = pet_tree_new_if_else(pe_cond, tree, tree_else);
	} else
		tree = pet_tree_new_if(pe_cond, tree);
	return tree;
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

	if ((!is_nested_allowed(cond, scop_then) ||
	     (has_else && !is_nested_allowed(cond, scop_else)))) {
		isl_pw_aff_free(cond);
		return scop_from_non_affine_if(tree, scop_then, scop_else,
					stmt_id, pc, state);
	}

	pet_context_free(pc);
	return scop_from_affine_if(tree, cond, scop_then, scop_else, state);
}

/* Try and construct a pet_tree for a label statement.
 * We currently only allow labels on expression statements.
 */
__isl_give pet_tree *PetScan::extract(LabelStmt *stmt)
{
	isl_id *label;
	pet_tree *tree;
	Stmt *sub;

	sub = stmt->getSubStmt();
	if (!isa<Expr>(sub)) {
		unsupported(stmt);
		return NULL;
	}

	label = isl_id_alloc(ctx, stmt->getName(), NULL);

	tree = extract(extract_expr(cast<Expr>(sub)), stmt->getSourceRange(),
			true);
	tree = pet_tree_set_label(tree, label);
	return tree;
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

/* Update the location of "tree" to include the source range of "stmt".
 *
 * Actually, we create a new location based on the source range of "stmt" and
 * then extend this new location to include the region of the original location.
 * This ensures that the line number of the final location refers to "stmt".
 */
__isl_give pet_tree *PetScan::update_loc(__isl_take pet_tree *tree, Stmt *stmt)
{
	pet_loc *loc, *tree_loc;

	tree_loc = pet_tree_get_loc(tree);
	loc = construct_pet_loc(stmt->getSourceRange(), false);
	loc = pet_loc_update_start_end_from_loc(loc, tree_loc);
	pet_loc_free(tree_loc);

	tree = pet_tree_set_loc(tree, loc);
	return tree;
}

/* Try and construct a pet_tree corresponding to "stmt".
 *
 * If "stmt" is a compound statement, then "skip_declarations"
 * indicates whether we should skip initial declarations in the
 * compound statement.
 *
 * If the constructed pet_tree is not a (possibly) partial representation
 * of "stmt", we update start and end of the pet_scop to those of "stmt".
 * In particular, if skip_declarations is set, then we may have skipped
 * declarations inside "stmt" and so the pet_scop may not represent
 * the entire "stmt".
 * Note that this function may be called with "stmt" referring to the entire
 * body of the function, including the outer braces.  In such cases,
 * skip_declarations will be set and the braces will not be taken into
 * account in tree->loc.
 */
__isl_give pet_tree *PetScan::extract(Stmt *stmt, bool skip_declarations)
{
	pet_tree *tree;

	if (isa<Expr>(stmt))
		return extract(extract_expr(cast<Expr>(stmt)),
				stmt->getSourceRange(), true);

	switch (stmt->getStmtClass()) {
	case Stmt::WhileStmtClass:
		tree = extract(cast<WhileStmt>(stmt));
		break;
	case Stmt::ForStmtClass:
		tree = extract_for(cast<ForStmt>(stmt));
		break;
	case Stmt::IfStmtClass:
		tree = extract(cast<IfStmt>(stmt));
		break;
	case Stmt::CompoundStmtClass:
		tree = extract(cast<CompoundStmt>(stmt), skip_declarations);
		break;
	case Stmt::LabelStmtClass:
		tree = extract(cast<LabelStmt>(stmt));
		break;
	case Stmt::ContinueStmtClass:
		tree = pet_tree_new_continue(ctx);
		break;
	case Stmt::BreakStmtClass:
		tree = pet_tree_new_break(ctx);
		break;
	case Stmt::DeclStmtClass:
		tree = extract(cast<DeclStmt>(stmt));
		break;
	default:
		unsupported(stmt);
		return NULL;
	}

	if (partial || skip_declarations)
		return tree;

	return update_loc(tree, stmt);
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
	if (!scop)
		return NULL;
	for (int i = 0; i < scop->n_array; ++i)
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
		pet_skip_info_seq_extract(&skip, state->int_size,
						&state->n_stmt, &state->n_test);
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

/* Try and construct a pet_tree corresponding to (part of)
 * a sequence of statements.
 *
 * "block" is set if the sequence respresents the children of
 * a compound statement.
 * "skip_declarations" is set if we should skip initial declarations
 * in the sequence of statements.
 *
 * If autodetect is set, then we allow the extraction of only a subrange
 * of the sequence of statements.  However, if there is at least one statement
 * for which we could not construct a scop and the final range contains
 * either no statements or at least one kill, then we discard the entire
 * range.
 */
__isl_give pet_tree *PetScan::extract(StmtRange stmt_range, bool block,
	bool skip_declarations)
{
	StmtIterator i;
	int j;
	bool has_kills = false;
	bool partial_range = false;
	pet_tree *tree;
	set<struct pet_stmt *> kills;
	set<struct pet_stmt *>::iterator it;

	for (i = stmt_range.first, j = 0; i != stmt_range.second; ++i, ++j)
		;

	tree = pet_tree_new_block(ctx, block, j);

	for (i = stmt_range.first; i != stmt_range.second; ++i) {
		Stmt *child = *i;
		pet_tree *tree_i;

		if (pet_tree_block_n_child(tree) == 0 && skip_declarations &&
		    child->getStmtClass() == Stmt::DeclStmtClass)
			continue;

		tree_i = extract(child);
		if (pet_tree_block_n_child(tree) != 0 && partial) {
			pet_tree_free(tree_i);
			break;
		}
		if (tree_i && child->getStmtClass() == Stmt::DeclStmtClass &&
		    block)
			has_kills = true;
		if (options->autodetect) {
			if (tree_i)
				tree = pet_tree_block_add_child(tree, tree_i);
			else
				partial_range = true;
			if (pet_tree_block_n_child(tree) != 0 && !tree_i)
				partial = true;
		} else {
			tree = pet_tree_block_add_child(tree, tree_i);
		}

		if (partial || !tree)
			break;
	}

	if (tree && partial_range) {
		if (pet_tree_block_n_child(tree) == 0 || has_kills) {
			pet_tree_free(tree);
			return NULL;
		}
		partial = true;
	}

	return tree;
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

extern "C" {
	static struct pet_array *extract_array(__isl_keep pet_expr *access,
		__isl_keep pet_context *pc, void *user);
}

/* Construct and return a pet_array corresponding to the variable
 * accessed by "access".
 * This function is used as a callback to pet_scop_from_pet_tree,
 * which is also passed a pointer to the PetScan object.
 */
static struct pet_array *extract_array(__isl_keep pet_expr *access,
	__isl_keep pet_context *pc, void *user)
{
	PetScan *ps = (PetScan *) user;
	isl_ctx *ctx;
	isl_id *id;
	ValueDecl *iv;

	ctx = pet_expr_get_ctx(access);
	id = pet_expr_access_get_id(access);
	iv = (ValueDecl *) isl_id_get_user(id);
	isl_id_free(id);
	return ps->extract_array(ctx, iv, NULL, pc);
}

/* Extract a pet_scop from "tree" within the context "pc".
 *
 * We simply call pet_scop_from_pet_tree with the appropriate arguments.
 */
struct pet_scop *PetScan::extract_scop(__isl_take pet_tree *tree,
	__isl_keep pet_context *pc)
{
	int int_size;

	int_size = ast_context.getTypeInfo(ast_context.IntTy).first / 8;

	return pet_scop_from_pet_tree(tree, int_size,
					&::extract_array, this, pc);
}

/* Check if the scop marked by the user is exactly this Stmt
 * or part of this Stmt.
 * If so, return a pet_scop corresponding to the marked region.
 * The pet_scop is created within the context "pc".
 * Otherwise, return NULL.
 */
struct pet_scop *PetScan::scan(Stmt *stmt, __isl_keep pet_context *pc)
{
	SourceManager &SM = PP.getSourceManager();
	unsigned start_off, end_off;

	start_off = getExpansionOffset(SM, stmt->getLocStart());
	end_off = getExpansionOffset(SM, stmt->getLocEnd());

	if (start_off > loc.end)
		return NULL;
	if (end_off < loc.start)
		return NULL;

	if (start_off >= loc.start && end_off <= loc.end)
		return extract_scop(extract(stmt), pc);

	StmtIterator start;
	for (start = stmt->child_begin(); start != stmt->child_end(); ++start) {
		Stmt *child = *start;
		if (!child)
			continue;
		start_off = getExpansionOffset(SM, child->getLocStart());
		end_off = getExpansionOffset(SM, child->getLocEnd());
		if (start_off < loc.start && end_off >= loc.end)
			return scan(child, pc);
		if (start_off >= loc.start)
			break;
	}

	StmtIterator end;
	for (end = start; end != stmt->child_end(); ++end) {
		Stmt *child = *end;
		start_off = SM.getFileOffset(child->getLocStart());
		if (start_off >= loc.end)
			break;
	}

	return extract_scop(extract(StmtRange(start, end), false, false), pc);
}

/* Set the size of index "pos" of "array" to "size".
 * In particular, add a constraint of the form
 *
 *	i_pos < size
 *
 * to array->extent and a constraint of the form
 *
 *	size >= 0
 *
 * to array->context.
 */
static struct pet_array *update_size(struct pet_array *array, int pos,
	__isl_take isl_pw_aff *size)
{
	isl_set *valid;
	isl_set *univ;
	isl_set *bound;
	isl_space *dim;
	isl_aff *aff;
	isl_pw_aff *index;
	isl_id *id;

	if (!array)
		goto error;

	valid = isl_set_params(isl_pw_aff_nonneg_set(isl_pw_aff_copy(size)));
	array->context = isl_set_intersect(array->context, valid);

	dim = isl_set_get_space(array->extent);
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient_si(aff, isl_dim_in, pos, 1);
	univ = isl_set_universe(isl_aff_get_domain_space(aff));
	index = isl_pw_aff_alloc(univ, aff);

	size = isl_pw_aff_add_dims(size, isl_dim_in,
				isl_set_dim(array->extent, isl_dim_set));
	id = isl_set_get_tuple_id(array->extent);
	size = isl_pw_aff_set_tuple_id(size, isl_dim_in, id);
	bound = isl_pw_aff_lt_set(index, size);

	array->extent = isl_set_intersect(array->extent, bound);

	if (!array->context || !array->extent)
		return pet_array_free(array);

	return array;
error:
	isl_pw_aff_free(size);
	return NULL;
}

/* Figure out the size of the array at position "pos" and all
 * subsequent positions from "type" and update the corresponding
 * argument of "expr" accordingly.
 */
__isl_give pet_expr *PetScan::set_upper_bounds(__isl_take pet_expr *expr,
	const Type *type, int pos)
{
	const ArrayType *atype;
	pet_expr *size;

	if (!expr)
		return NULL;

	if (type->isPointerType()) {
		type = type->getPointeeType().getTypePtr();
		return set_upper_bounds(expr, type, pos + 1);
	}
	if (!type->isArrayType())
		return expr;

	type = type->getCanonicalTypeInternal().getTypePtr();
	atype = cast<ArrayType>(type);

	if (type->isConstantArrayType()) {
		const ConstantArrayType *ca = cast<ConstantArrayType>(atype);
		size = extract_expr(ca->getSize());
		expr = pet_expr_set_arg(expr, pos, size);
	} else if (type->isVariableArrayType()) {
		const VariableArrayType *vla = cast<VariableArrayType>(atype);
		size = extract_expr(vla->getSizeExpr());
		expr = pet_expr_set_arg(expr, pos, size);
	}

	type = atype->getElementType().getTypePtr();

	return set_upper_bounds(expr, type, pos + 1);
}

/* Does "expr" represent the "integer" infinity?
 */
static int is_infty(__isl_keep pet_expr *expr)
{
	isl_val *v;
	int res;

	if (pet_expr_get_type(expr) != pet_expr_int)
		return 0;
	v = pet_expr_int_get_val(expr);
	res = isl_val_is_infty(v);
	isl_val_free(v);

	return res;
}

/* Figure out the dimensions of an array "array" based on its type
 * "type" and update "array" accordingly.
 *
 * We first construct a pet_expr that holds the sizes of the array
 * in each dimension.  The expression is initialized to infinity
 * and updated from the type.
 *
 * The arguments of the size expression that have been updated
 * are then converted to an affine expression within the context "pc" and
 * incorporated into the size of "array".  If we are unable to convert
 * a size expression to an affine expression, then we leave
 * the corresponding size of "array" untouched.
 */
struct pet_array *PetScan::set_upper_bounds(struct pet_array *array,
	const Type *type, __isl_keep pet_context *pc)
{
	int depth = array_depth(type);
	pet_expr *expr, *inf;

	if (!array)
		return NULL;

	inf = pet_expr_new_int(isl_val_infty(ctx));
	expr = pet_expr_new_call(ctx, "bounds", depth);
	for (int i = 0; i < depth; ++i)
		expr = pet_expr_set_arg(expr, i, pet_expr_copy(inf));
	pet_expr_free(inf);

	expr = set_upper_bounds(expr, type, 0);

	for (int i = 0; i < depth; ++i) {
		pet_expr *arg;
		isl_pw_aff *size;

		arg = pet_expr_get_arg(expr, i);
		if (!is_infty(arg)) {
			size = pet_expr_extract_affine(arg, pc);
			if (!size)
				array = pet_array_free(array);
			else if (isl_pw_aff_involves_nan(size))
				isl_pw_aff_free(size);
			else
				array = update_size(array, i, size);
		}
		pet_expr_free(arg);
	}
	pet_expr_free(expr);

	return array;
}

/* Is "T" the type of a variable length array with static size?
 */
static bool is_vla_with_static_size(QualType T)
{
	const VariableArrayType *vlatype;

	if (!T->isVariableArrayType())
		return false;
	vlatype = cast<VariableArrayType>(T);
	return vlatype->getSizeModifier() == VariableArrayType::Static;
}

/* Return the type of "decl" as an array.
 *
 * In particular, if "decl" is a parameter declaration that
 * is a variable length array with a static size, then
 * return the original type (i.e., the variable length array).
 * Otherwise, return the type of decl.
 */
static QualType get_array_type(ValueDecl *decl)
{
	ParmVarDecl *parm;
	QualType T;

	parm = dyn_cast<ParmVarDecl>(decl);
	if (!parm)
		return decl->getType();

	T = parm->getOriginalType();
	if (!is_vla_with_static_size(T))
		return decl->getType();
	return T;
}

/* Does "decl" have definition that we can keep track of in a pet_type?
 */
static bool has_printable_definition(RecordDecl *decl)
{
	if (!decl->getDeclName())
		return false;
	return decl->getLexicalDeclContext() == decl->getDeclContext();
}

/* Construct and return a pet_array corresponding to the variable "decl".
 * In particular, initialize array->extent to
 *
 *	{ name[i_1,...,i_d] : i_1,...,i_d >= 0 }
 *
 * and then call set_upper_bounds to set the upper bounds on the indices
 * based on the type of the variable.  The upper bounds are converted
 * to affine expressions within the context "pc".
 *
 * If the base type is that of a record with a top-level definition and
 * if "types" is not null, then the RecordDecl corresponding to the type
 * is added to "types".
 *
 * If the base type is that of a record with no top-level definition,
 * then we replace it by "<subfield>".
 */
struct pet_array *PetScan::extract_array(isl_ctx *ctx, ValueDecl *decl,
	lex_recorddecl_set *types, __isl_keep pet_context *pc)
{
	struct pet_array *array;
	QualType qt = get_array_type(decl);
	const Type *type = qt.getTypePtr();
	int depth = array_depth(type);
	QualType base = pet_clang_base_type(qt);
	string name;
	isl_id *id;
	isl_space *dim;

	array = isl_calloc_type(ctx, struct pet_array);
	if (!array)
		return NULL;

	id = create_decl_id(ctx, decl);
	dim = isl_space_set_alloc(ctx, 0, depth);
	dim = isl_space_set_tuple_id(dim, isl_dim_set, id);

	array->extent = isl_set_nat_universe(dim);

	dim = isl_space_params_alloc(ctx, 0);
	array->context = isl_set_universe(dim);

	array = set_upper_bounds(array, type, pc);
	if (!array)
		return NULL;

	name = base.getAsString();

	if (types && base->isRecordType()) {
		RecordDecl *decl = pet_clang_record_decl(base);
		if (has_printable_definition(decl))
			types->insert(decl);
		else
			name = "<subfield>";
	}

	array->element_type = strdup(name.c_str());
	array->element_is_record = base->isRecordType();
	array->element_size = decl->getASTContext().getTypeInfo(base).first / 8;

	return array;
}

/* Construct and return a pet_array corresponding to the sequence
 * of declarations "decls".
 * The upper bounds of the array are converted to affine expressions
 * within the context "pc".
 * If the sequence contains a single declaration, then it corresponds
 * to a simple array access.  Otherwise, it corresponds to a member access,
 * with the declaration for the substructure following that of the containing
 * structure in the sequence of declarations.
 * We start with the outermost substructure and then combine it with
 * information from the inner structures.
 *
 * Additionally, keep track of all required types in "types".
 */
struct pet_array *PetScan::extract_array(isl_ctx *ctx,
	vector<ValueDecl *> decls, lex_recorddecl_set *types,
	__isl_keep pet_context *pc)
{
	struct pet_array *array;
	vector<ValueDecl *>::iterator it;

	it = decls.begin();

	array = extract_array(ctx, *it, types, pc);

	for (++it; it != decls.end(); ++it) {
		struct pet_array *parent;
		const char *base_name, *field_name;
		char *product_name;

		parent = array;
		array = extract_array(ctx, *it, types, pc);
		if (!array)
			return pet_array_free(parent);

		base_name = isl_set_get_tuple_name(parent->extent);
		field_name = isl_set_get_tuple_name(array->extent);
		product_name = pet_array_member_access_name(ctx,
							base_name, field_name);

		array->extent = isl_set_product(isl_set_copy(parent->extent),
						array->extent);
		if (product_name)
			array->extent = isl_set_set_tuple_name(array->extent,
								product_name);
		array->context = isl_set_intersect(array->context,
						isl_set_copy(parent->context));

		pet_array_free(parent);
		free(product_name);

		if (!array->extent || !array->context || !product_name)
			return pet_array_free(array);
	}

	return array;
}

/* Add a pet_type corresponding to "decl" to "scop, provided
 * it is a member of "types" and it has not been added before
 * (i.e., it is not a member of "types_done".
 *
 * Since we want the user to be able to print the types
 * in the order in which they appear in the scop, we need to
 * make sure that types of fields in a structure appear before
 * that structure.  We therefore call ourselves recursively
 * on the types of all record subfields.
 */
static struct pet_scop *add_type(isl_ctx *ctx, struct pet_scop *scop,
	RecordDecl *decl, Preprocessor &PP, lex_recorddecl_set &types,
	lex_recorddecl_set &types_done)
{
	string s;
	llvm::raw_string_ostream S(s);
	RecordDecl::field_iterator it;

	if (types.find(decl) == types.end())
		return scop;
	if (types_done.find(decl) != types_done.end())
		return scop;

	for (it = decl->field_begin(); it != decl->field_end(); ++it) {
		RecordDecl *record;
		QualType type = it->getType();

		if (!type->isRecordType())
			continue;
		record = pet_clang_record_decl(type);
		scop = add_type(ctx, scop, record, PP, types, types_done);
	}

	if (strlen(decl->getName().str().c_str()) == 0)
		return scop;

	decl->print(S, PrintingPolicy(PP.getLangOpts()));
	S.str();

	scop->types[scop->n_type] = pet_type_alloc(ctx,
				    decl->getName().str().c_str(), s.c_str());
	if (!scop->types[scop->n_type])
		return pet_scop_free(scop);

	types_done.insert(decl);

	scop->n_type++;

	return scop;
}

/* Construct a list of pet_arrays, one for each array (or scalar)
 * accessed inside "scop", add this list to "scop" and return the result.
 * The upper bounds of the arrays are converted to affine expressions
 * within the context "pc".
 *
 * The context of "scop" is updated with the intersection of
 * the contexts of all arrays, i.e., constraints on the parameters
 * that ensure that the arrays have a valid (non-negative) size.
 *
 * If the any of the extracted arrays refers to a member access,
 * then also add the required types to "scop".
 */
struct pet_scop *PetScan::scan_arrays(struct pet_scop *scop,
	__isl_keep pet_context *pc)
{
	int i;
	array_desc_set arrays;
	array_desc_set::iterator it;
	lex_recorddecl_set types;
	lex_recorddecl_set types_done;
	lex_recorddecl_set::iterator types_it;
	int n_array;
	struct pet_array **scop_arrays;

	if (!scop)
		return NULL;

	pet_scop_collect_arrays(scop, arrays);
	if (arrays.size() == 0)
		return scop;

	n_array = scop->n_array;

	scop_arrays = isl_realloc_array(ctx, scop->arrays, struct pet_array *,
					n_array + arrays.size());
	if (!scop_arrays)
		goto error;
	scop->arrays = scop_arrays;

	for (it = arrays.begin(), i = 0; it != arrays.end(); ++it, ++i) {
		struct pet_array *array;
		array = extract_array(ctx, *it, &types, pc);
		scop->arrays[n_array + i] = array;
		if (!scop->arrays[n_array + i])
			goto error;
		scop->n_array++;
		scop->context = isl_set_intersect(scop->context,
						isl_set_copy(array->context));
		if (!scop->context)
			goto error;
	}

	if (types.size() == 0)
		return scop;

	scop->types = isl_alloc_array(ctx, struct pet_type *, types.size());
	if (!scop->types)
		goto error;

	for (types_it = types.begin(); types_it != types.end(); ++types_it)
		scop = add_type(ctx, scop, *types_it, PP, types, types_done);

	return scop;
error:
	pet_scop_free(scop);
	return NULL;
}

/* Bound all parameters in scop->context to the possible values
 * of the corresponding C variable.
 */
static struct pet_scop *add_parameter_bounds(struct pet_scop *scop)
{
	int n;

	if (!scop)
		return NULL;

	n = isl_set_dim(scop->context, isl_dim_param);
	for (int i = 0; i < n; ++i) {
		isl_id *id;
		ValueDecl *decl;

		id = isl_set_get_dim_id(scop->context, isl_dim_param, i);
		if (pet_nested_in_id(id)) {
			isl_id_free(id);
			isl_die(isl_set_get_ctx(scop->context),
				isl_error_internal,
				"unresolved nested parameter", goto error);
		}
		decl = (ValueDecl *) isl_id_get_user(id);
		isl_id_free(id);

		scop->context = set_parameter_bounds(scop->context, i, decl);

		if (!scop->context)
			goto error;
	}

	return scop;
error:
	pet_scop_free(scop);
	return NULL;
}

/* Construct a pet_scop from the given function.
 *
 * If the scop was delimited by scop and endscop pragmas, then we override
 * the file offsets by those derived from the pragmas.
 */
struct pet_scop *PetScan::scan(FunctionDecl *fd)
{
	pet_scop *scop;
	Stmt *stmt;
	pet_context *pc;

	stmt = fd->getBody();

	pc = pet_context_alloc(isl_space_set_alloc(ctx, 0, 0));
	if (options->autodetect) {
		scop = extract_scop(extract(stmt, true), pc);
	} else {
		scop = scan(stmt, pc);
		scop = pet_scop_update_start_end(scop, loc.start, loc.end);
	}
	scop = pet_scop_detect_parameter_accesses(scop);
	scop = scan_arrays(scop, pc);
	pet_context_free(pc);
	scop = add_parameter_bounds(scop);
	scop = pet_scop_gist(scop, value_bounds);

	return scop;
}
