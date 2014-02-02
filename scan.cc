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
#include "nest.h"
#include "options.h"
#include "scan.h"
#include "scop.h"
#include "scop_plus.h"
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
	std::map<const Type *, pet_expr *>::iterator it;

	for (it = type_size.begin(); it != type_size.end(); ++it)
		pet_expr_free(it->second);

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

/* Extract an integer from "val", which is assumed to be non-negative.
 */
static __isl_give isl_val *extract_unsigned(isl_ctx *ctx,
	const llvm::APInt &val)
{
	unsigned n;
	const uint64_t *data;

	data = val.getRawData();
	n = val.getNumWords();
	return isl_val_int_from_chunks(ctx, n, sizeof(uint64_t), data);
}

/* Extract an integer from "val".  If "is_signed" is set, then "val"
 * is signed.  Otherwise it it unsigned.
 */
static __isl_give isl_val *extract_int(isl_ctx *ctx, bool is_signed,
	llvm::APInt val)
{
	int is_negative = is_signed && val.isNegative();
	isl_val *v;

	if (is_negative)
		val = -val;

	v = extract_unsigned(ctx, val);

	if (is_negative)
		v = isl_val_neg(v);
	return v;
}

/* Extract an integer from "expr".
 */
__isl_give isl_val *PetScan::extract_int(isl_ctx *ctx, IntegerLiteral *expr)
{
	const Type *type = expr->getType().getTypePtr();
	bool is_signed = type->hasSignedIntegerRepresentation();

	return ::extract_int(ctx, is_signed, expr->getValue());
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
 *
 * If "expr" references an enum constant, then return an integer expression
 * instead, representing the value of the enum constant.
 */
__isl_give pet_expr *PetScan::extract_index_expr(DeclRefExpr *expr)
{
	return extract_index_expr(expr->getDecl());
}

/* Construct a pet_expr representing an index expression for an access
 * to the variable "decl".
 *
 * If "decl" is an enum constant, then we return an integer expression
 * instead, representing the value of the enum constant.
 */
__isl_give pet_expr *PetScan::extract_index_expr(ValueDecl *decl)
{
	isl_id *id;
	isl_space *space;

	if (isa<EnumConstantDecl>(decl))
		return extract_expr(cast<EnumConstantDecl>(decl));

	id = create_decl_id(ctx, decl);
	space = isl_space_alloc(ctx, 0, 0, 0);
	space = isl_space_set_tuple_id(space, isl_dim_out, id);

	return pet_expr_from_index(isl_multi_pw_aff_zero(space));
}

/* Construct a pet_expr representing the index expression "expr"
 * Return NULL on error.
 *
 * If "expr" is a reference to an enum constant, then return
 * an integer expression instead, representing the value of the enum constant.
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
 *
 * If "expr" is a reference to an enum constant, then return
 * an integer expression instead, representing the value of the enum constant.
 */
__isl_give pet_expr *PetScan::extract_access_expr(Expr *expr)
{
	pet_expr *index;

	index = extract_index_expr(expr);

	if (pet_expr_get_type(index) == pet_expr_int)
		return index;

	return extract_access_expr(expr->getType(), index);
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

/* Construct a pet_expr representing the integer enum constant "ecd".
 */
__isl_give pet_expr *PetScan::extract_expr(EnumConstantDecl *ecd)
{
	isl_val *v;
	const llvm::APSInt &init = ecd->getInitVal();
	v = ::extract_int(ctx, init.isSigned(), init);
	return pet_expr_new_int(v);
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
	int independent;
	int declared;
	pet_expr *pe_init, *pe_inc, *pe_iv, *pe_cond;

	independent = is_current_stmt_marked_independent();

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
	tree = pet_tree_new_for(independent, declared, pe_iv, pe_init, pe_cond,
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
 * a location referring to the start of the line and set *indent
 * to the indentation of "loc"
 * Otherwise, return "loc" and set *indent to "".
 *
 * This function is used to extend a scop to the start of the line
 * if the first token of the scop is also the first token on the line.
 *
 * We look for the first token on the line.  If its location is equal to "loc",
 * then the latter is the location of the first token on the line.
 */
static SourceLocation move_to_start_of_line_if_first_token(SourceLocation loc,
	SourceManager &SM, const LangOptions &LO, char **indent)
{
	std::pair<FileID, unsigned> file_offset_pair;
	llvm::StringRef file;
	const char *pos;
	Token tok;
	SourceLocation token_loc, line_loc;
	int col;
	const char *s;

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

	s = SM.getCharacterData(line_loc);
	*indent = strndup(s, token_loc == loc ? col - 1 : 0);

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
	char *indent;

	loc = move_to_start_of_line_if_first_token(loc, SM, LO, &indent);
	start = getExpansionOffset(SM, loc);
	loc = range.getEnd();
	if (skip_semi)
		loc = location_after_semi(loc, SM, LO);
	else
		loc = PP.getLocForEndOfToken(loc);
	end = getExpansionOffset(SM, loc);

	return pet_loc_alloc(ctx, start, end, line, indent);
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

	set_current_stmt(stmt);

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

extern "C" {
	static __isl_give pet_expr *get_array_size(__isl_keep pet_expr *access,
		void *user);
	static struct pet_array *extract_array(__isl_keep pet_expr *access,
		__isl_keep pet_context *pc, void *user);
}

/* Construct a pet_expr that holds the sizes of the array accessed
 * by "access".
 * This function is used as a callback to pet_context_add_parameters,
 * which is also passed a pointer to the PetScan object.
 */
static __isl_give pet_expr *get_array_size(__isl_keep pet_expr *access,
	void *user)
{
	PetScan *ps = (PetScan *) user;
	isl_id *id;
	ValueDecl *decl;
	const Type *type;

	id = pet_expr_access_get_id(access);
	decl = (ValueDecl *) isl_id_get_user(id);
	isl_id_free(id);
	type = get_array_type(decl).getTypePtr();
	return ps->get_array_size(type);
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

/* Extract a pet_scop from "tree".
 *
 * We simply call pet_scop_from_pet_tree with the appropriate arguments and
 * then add pet_arrays for all accessed arrays.
 * We populate the pet_context with assignments for all parameters used
 * inside "tree" or any of the size expressions for the arrays accessed
 * by "tree" so that they can be used in affine expressions.
 */
struct pet_scop *PetScan::extract_scop(__isl_take pet_tree *tree)
{
	int int_size;
	isl_set *domain;
	pet_context *pc;
	pet_scop *scop;

	int_size = ast_context.getTypeInfo(ast_context.IntTy).first / 8;

	domain = isl_set_universe(isl_space_set_alloc(ctx, 0, 0));
	pc = pet_context_alloc(domain);
	pc = pet_context_add_parameters(pc, tree, &::get_array_size, this);
	scop = pet_scop_from_pet_tree(tree, int_size,
					&::extract_array, this, pc);
	scop = scan_arrays(scop, pc);
	pet_context_free(pc);

	return scop;
}

/* Check if the scop marked by the user is exactly this Stmt
 * or part of this Stmt.
 * If so, return a pet_scop corresponding to the marked region.
 * Otherwise, return NULL.
 */
struct pet_scop *PetScan::scan(Stmt *stmt)
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
		return extract_scop(extract(stmt));

	StmtIterator start;
	for (start = stmt->child_begin(); start != stmt->child_end(); ++start) {
		Stmt *child = *start;
		if (!child)
			continue;
		start_off = getExpansionOffset(SM, child->getLocStart());
		end_off = getExpansionOffset(SM, child->getLocEnd());
		if (start_off < loc.start && end_off >= loc.end)
			return scan(child);
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

	return extract_scop(extract(StmtRange(start, end), false, false));
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

/* Construct a pet_expr that holds the sizes of an array of the given type.
 * The returned expression is a call expression with as arguments
 * the sizes in each dimension.  If we are unable to derive the size
 * in a given dimension, then the corresponding argument is set to infinity.
 * In fact, we initialize all arguments to infinity and then update
 * them if we are able to figure out the size.
 *
 * The result is stored in the type_size cache so that we can reuse
 * it if this method gets called on the same type again later on.
 */
__isl_give pet_expr *PetScan::get_array_size(const Type *type)
{
	int depth;
	pet_expr *expr, *inf;

	if (type_size.find(type) != type_size.end())
		return pet_expr_copy(type_size[type]);

	depth = array_depth(type);
	inf = pet_expr_new_int(isl_val_infty(ctx));
	expr = pet_expr_new_call(ctx, "bounds", depth);
	for (int i = 0; i < depth; ++i)
		expr = pet_expr_set_arg(expr, i, pet_expr_copy(inf));
	pet_expr_free(inf);

	expr = set_upper_bounds(expr, type, 0);
	type_size[type] = pet_expr_copy(expr);

	return expr;
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
 * in each dimension.  The resulting expression may containing
 * infinity values for dimension where we are unable to derive
 * a size expression.
 *
 * The arguments of the size expression that have a value different from
 * infinity are then converted to an affine expression
 * within the context "pc" and incorporated into the size of "array".
 * If we are unable to convert a size expression to an affine expression,
 * then we leave the corresponding size of "array" untouched.
 */
struct pet_array *PetScan::set_upper_bounds(struct pet_array *array,
	const Type *type, __isl_keep pet_context *pc)
{
	int n;
	pet_expr *expr;

	if (!array)
		return NULL;

	expr = get_array_size(type);

	n = pet_expr_get_n_arg(expr);
	for (int i = 0; i < n; ++i) {
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

	stmt = fd->getBody();

	if (options->autodetect) {
		set_current_stmt(stmt);
		scop = extract_scop(extract(stmt, true));
	} else {
		current_line = loc.start_line;
		scop = scan(stmt);
		scop = pet_scop_update_start_end(scop, loc.start, loc.end);
	}
	scop = add_parameter_bounds(scop);
	scop = pet_scop_gist(scop, value_bounds);

	return scop;
}

/* Update this->last_line and this->current_line based on the fact
 * that we are about to consider "stmt".
 */
void PetScan::set_current_stmt(Stmt *stmt)
{
	SourceLocation loc = stmt->getLocStart();
	SourceManager &SM = PP.getSourceManager();

	last_line = current_line;
	current_line = SM.getExpansionLineNumber(loc);
}

/* Is the current statement marked by an independent pragma?
 * That is, is there an independent pragma on a line between
 * the line of the current statement and the line of the previous statement.
 * The search is not implemented very efficiently.  We currently
 * assume that there are only a few independent pragmas, if any.
 */
bool PetScan::is_current_stmt_marked_independent()
{
	for (int i = 0; i < independent.size(); ++i) {
		unsigned line = independent[i].line;

		if (last_line < line && line < current_line)
			return true;
	}

	return false;
}
