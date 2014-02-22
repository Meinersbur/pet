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
#include "clang.h"
#include "expr.h"
#include "nest.h"
#include "options.h"
#include "scan.h"
#include "scop.h"
#include "scop_plus.h"
#include "skip.h"

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

/* Mark "decl" as having an unknown value in "assigned_value".
 *
 * If no (known or unknown) value was assigned to "decl" before,
 * then it may have been treated as a parameter before and may
 * therefore appear in a value assigned to another variable.
 * If so, this assignment needs to be turned into an unknown value too.
 */
static void clear_assignment(map<ValueDecl *, isl_pw_aff *> &assigned_value,
	ValueDecl *decl)
{
	map<ValueDecl *, isl_pw_aff *>::iterator it;

	it = assigned_value.find(decl);

	assigned_value[decl] = NULL;

	if (it != assigned_value.end())
		return;

	for (it = assigned_value.begin(); it != assigned_value.end(); ++it) {
		isl_pw_aff *pa = it->second;
		int nparam = isl_pw_aff_dim(pa, isl_dim_param);

		for (int i = 0; i < nparam; ++i) {
			isl_id *id;

			if (!isl_pw_aff_has_dim_id(pa, isl_dim_param, i))
				continue;
			id = isl_pw_aff_get_dim_id(pa, isl_dim_param, i);
			if (isl_id_get_user(id) == decl)
				it->second = NULL;
			isl_id_free(id);
		}
	}
}

/* Look for any assignments to scalar variables in part of the parse
 * tree and set assigned_value to NULL for each of them.
 * Also reset assigned_value if the address of a scalar variable
 * is being taken.  As an exception, if the address is passed to a function
 * that is declared to receive a const pointer, then assigned_value is
 * not reset.
 *
 * This ensures that we won't use any previously stored value
 * in the current subtree and its parents.
 */
struct clear_assignments : RecursiveASTVisitor<clear_assignments> {
	map<ValueDecl *, isl_pw_aff *> &assigned_value;
	set<UnaryOperator *> skip;

	clear_assignments(map<ValueDecl *, isl_pw_aff *> &assigned_value) :
		assigned_value(assigned_value) {}

	/* Check for "address of" operators whose value is passed
	 * to a const pointer argument and add them to "skip", so that
	 * we can skip them in VisitUnaryOperator.
	 */
	bool VisitCallExpr(CallExpr *expr) {
		FunctionDecl *fd;
		fd = expr->getDirectCallee();
		if (!fd)
			return true;
		for (int i = 0; i < expr->getNumArgs(); ++i) {
			Expr *arg = expr->getArg(i);
			UnaryOperator *op;
			if (arg->getStmtClass() == Stmt::ImplicitCastExprClass) {
				ImplicitCastExpr *ice;
				ice = cast<ImplicitCastExpr>(arg);
				arg = ice->getSubExpr();
			}
			if (arg->getStmtClass() != Stmt::UnaryOperatorClass)
				continue;
			op = cast<UnaryOperator>(arg);
			if (op->getOpcode() != UO_AddrOf)
				continue;
			if (const_base(fd->getParamDecl(i)->getType()))
				skip.insert(op);
		}
		return true;
	}

	bool VisitUnaryOperator(UnaryOperator *expr) {
		Expr *arg;
		DeclRefExpr *ref;
		ValueDecl *decl;

		switch (expr->getOpcode()) {
		case UO_AddrOf:
		case UO_PostInc:
		case UO_PostDec:
		case UO_PreInc:
		case UO_PreDec:
			break;
		default:
			return true;
		}
		if (skip.find(expr) != skip.end())
			return true;

		arg = expr->getSubExpr();
		if (arg->getStmtClass() != Stmt::DeclRefExprClass)
			return true;
		ref = cast<DeclRefExpr>(arg);
		decl = ref->getDecl();
		clear_assignment(assigned_value, decl);
		return true;
	}

	bool VisitBinaryOperator(BinaryOperator *expr) {
		Expr *lhs;
		DeclRefExpr *ref;
		ValueDecl *decl;

		if (!expr->isAssignmentOp())
			return true;
		lhs = expr->getLHS();
		if (lhs->getStmtClass() != Stmt::DeclRefExprClass)
			return true;
		ref = cast<DeclRefExpr>(lhs);
		decl = ref->getDecl();
		clear_assignment(assigned_value, decl);
		return true;
	}
};

/* Keep a copy of the currently assigned values.
 *
 * Any variable that is assigned a value inside the current scope
 * is removed again when we leave the scope (either because it wasn't
 * stored in the cache or because it has a different value in the cache).
 */
struct assigned_value_cache {
	map<ValueDecl *, isl_pw_aff *> &assigned_value;
	map<ValueDecl *, isl_pw_aff *> cache;

	assigned_value_cache(map<ValueDecl *, isl_pw_aff *> &assigned_value) :
		assigned_value(assigned_value), cache(assigned_value) {}
	~assigned_value_cache() {
		map<ValueDecl *, isl_pw_aff *>::iterator it = cache.begin();
		for (it = assigned_value.begin(); it != assigned_value.end();
		     ++it) {
			if (!it->second ||
			    (cache.find(it->first) != cache.end() &&
			     cache[it->first] != it->second))
				cache[it->first] = NULL;
		}
		assigned_value = cache;
	}
};

/* Insert an expression into the collection of expressions,
 * provided it is not already in there.
 * The isl_pw_affs are freed in the destructor.
 */
void PetScan::insert_expression(__isl_take isl_pw_aff *expr)
{
	std::set<isl_pw_aff *>::iterator it;

	if (expressions.find(expr) == expressions.end())
		expressions.insert(expr);
	else
		isl_pw_aff_free(expr);
}

PetScan::~PetScan()
{
	std::set<isl_pw_aff *>::iterator it;

	for (it = expressions.begin(); it != expressions.end(); ++it)
		isl_pw_aff_free(*it);

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

/* Extract an affine expression from the IntegerLiteral "expr".
 */
__isl_give isl_pw_aff *PetScan::extract_affine(IntegerLiteral *expr)
{
	isl_space *space = isl_space_params_alloc(ctx, 0);
	isl_local_space *ls = isl_local_space_from_space(isl_space_copy(space));
	isl_aff *aff = isl_aff_zero_on_domain(ls);
	isl_set *dom = isl_set_universe(space);
	isl_val *v;

	v = extract_int(expr);
	aff = isl_aff_add_constant_val(aff, v);

	return isl_pw_aff_alloc(dom, aff);
}

/* Extract an affine expression from the APInt "val", which is assumed
 * to be non-negative.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(const llvm::APInt &val)
{
	isl_space *dim = isl_space_params_alloc(ctx, 0);
	isl_local_space *ls = isl_local_space_from_space(isl_space_copy(dim));
	isl_aff *aff = isl_aff_zero_on_domain(ls);
	isl_set *dom = isl_set_universe(dim);
	isl_val *v;

	v = extract_unsigned(ctx, val);
	aff = isl_aff_add_constant_val(aff, v);

	return isl_pw_aff_alloc(dom, aff);
}

__isl_give isl_pw_aff *PetScan::extract_affine(ImplicitCastExpr *expr)
{
	return extract_affine(expr->getSubExpr());
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

/* Extract an affine expression from the DeclRefExpr "expr".
 *
 * If the variable has been assigned a value, then we check whether
 * we know what (affine) value was assigned.
 * If so, we return this value.  Otherwise we convert "expr"
 * to an extra parameter (provided nesting_enabled is set).
 *
 * Otherwise, we simply return an expression that is equal
 * to a parameter corresponding to the referenced variable.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(DeclRefExpr *expr)
{
	ValueDecl *decl = expr->getDecl();
	const Type *type = decl->getType().getTypePtr();
	isl_id *id;
	isl_space *dim;
	isl_aff *aff;
	isl_set *dom;

	if (!type->isIntegerType()) {
		unsupported(expr);
		return NULL;
	}

	if (assigned_value.find(decl) != assigned_value.end()) {
		if (assigned_value[decl])
			return isl_pw_aff_copy(assigned_value[decl]);
		else
			return nested_access(expr);
	}

	id = isl_id_alloc(ctx, decl->getName().str().c_str(), decl);
	dim = isl_space_params_alloc(ctx, 1);

	dim = isl_space_set_dim_id(dim, isl_dim_param, 0, id);

	dom = isl_set_universe(isl_space_copy(dim));
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient_si(aff, isl_dim_param, 0, 1);

	return isl_pw_aff_alloc(dom, aff);
}

/* Extract an affine expression from an integer division operation.
 * In particular, if "expr" is lhs/rhs, then return
 *
 *	lhs >= 0 ? floor(lhs/rhs) : ceil(lhs/rhs)
 *
 * The second argument (rhs) is required to be a (positive) integer constant.
 */
__isl_give isl_pw_aff *PetScan::extract_affine_div(BinaryOperator *expr)
{
	int is_cst;
	isl_pw_aff *rhs, *lhs;

	rhs = extract_affine(expr->getRHS());
	is_cst = isl_pw_aff_is_cst(rhs);
	if (is_cst < 0 || !is_cst) {
		isl_pw_aff_free(rhs);
		if (!is_cst)
			unsupported(expr);
		return NULL;
	}

	lhs = extract_affine(expr->getLHS());

	return isl_pw_aff_tdiv_q(lhs, rhs);
}

/* Extract an affine expression from a modulo operation.
 * In particular, if "expr" is lhs/rhs, then return
 *
 *	lhs - rhs * (lhs >= 0 ? floor(lhs/rhs) : ceil(lhs/rhs))
 *
 * The second argument (rhs) is required to be a (positive) integer constant.
 */
__isl_give isl_pw_aff *PetScan::extract_affine_mod(BinaryOperator *expr)
{
	int is_cst;
	isl_pw_aff *rhs, *lhs;

	rhs = extract_affine(expr->getRHS());
	is_cst = isl_pw_aff_is_cst(rhs);
	if (is_cst < 0 || !is_cst) {
		isl_pw_aff_free(rhs);
		if (!is_cst)
			unsupported(expr);
		return NULL;
	}

	lhs = extract_affine(expr->getLHS());

	return isl_pw_aff_tdiv_r(lhs, rhs);
}

/* Extract an affine expression from a multiplication operation.
 * This is only allowed if at least one of the two arguments
 * is a (piecewise) constant.
 */
__isl_give isl_pw_aff *PetScan::extract_affine_mul(BinaryOperator *expr)
{
	isl_pw_aff *lhs;
	isl_pw_aff *rhs;

	lhs = extract_affine(expr->getLHS());
	rhs = extract_affine(expr->getRHS());

	if (!isl_pw_aff_is_cst(lhs) && !isl_pw_aff_is_cst(rhs)) {
		isl_pw_aff_free(lhs);
		isl_pw_aff_free(rhs);
		unsupported(expr);
		return NULL;
	}

	return isl_pw_aff_mul(lhs, rhs);
}

/* Extract an affine expression from an addition or subtraction operation.
 */
__isl_give isl_pw_aff *PetScan::extract_affine_add(BinaryOperator *expr)
{
	isl_pw_aff *lhs;
	isl_pw_aff *rhs;

	lhs = extract_affine(expr->getLHS());
	rhs = extract_affine(expr->getRHS());

	switch (expr->getOpcode()) {
	case BO_Add:
		return isl_pw_aff_add(lhs, rhs);
	case BO_Sub:
		return isl_pw_aff_sub(lhs, rhs);
	default:
		isl_pw_aff_free(lhs);
		isl_pw_aff_free(rhs);
		return NULL;
	}

}

/* Compute
 *
 *	pwaff mod 2^width
 */
static __isl_give isl_pw_aff *wrap(__isl_take isl_pw_aff *pwaff,
	unsigned width)
{
	isl_ctx *ctx;
	isl_val *mod;

	ctx = isl_pw_aff_get_ctx(pwaff);
	mod = isl_val_int_from_ui(ctx, width);
	mod = isl_val_2exp(mod);

	pwaff = isl_pw_aff_mod_val(pwaff, mod);

	return pwaff;
}

/* Limit the domain of "pwaff" to those elements where the function
 * value satisfies
 *
 *	2^{width-1} <= pwaff < 2^{width-1}
 */
static __isl_give isl_pw_aff *avoid_overflow(__isl_take isl_pw_aff *pwaff,
	unsigned width)
{
	isl_ctx *ctx;
	isl_val *v;
	isl_space *space = isl_pw_aff_get_domain_space(pwaff);
	isl_local_space *ls = isl_local_space_from_space(space);
	isl_aff *bound;
	isl_set *dom;
	isl_pw_aff *b;

	ctx = isl_pw_aff_get_ctx(pwaff);
	v = isl_val_int_from_ui(ctx, width - 1);
	v = isl_val_2exp(v);

	bound = isl_aff_zero_on_domain(ls);
	bound = isl_aff_add_constant_val(bound, v);
	b = isl_pw_aff_from_aff(bound);

	dom = isl_pw_aff_lt_set(isl_pw_aff_copy(pwaff), isl_pw_aff_copy(b));
	pwaff = isl_pw_aff_intersect_domain(pwaff, dom);

	b = isl_pw_aff_neg(b);
	dom = isl_pw_aff_ge_set(isl_pw_aff_copy(pwaff), b);
	pwaff = isl_pw_aff_intersect_domain(pwaff, dom);

	return pwaff;
}

/* Handle potential overflows on signed computations.
 *
 * If options->signed_overflow is set to PET_OVERFLOW_AVOID,
 * the we adjust the domain of "pa" to avoid overflows.
 */
__isl_give isl_pw_aff *PetScan::signed_overflow(__isl_take isl_pw_aff *pa,
	unsigned width)
{
	if (options->signed_overflow == PET_OVERFLOW_AVOID)
		pa = avoid_overflow(pa, width);

	return pa;
}

/* Return the piecewise affine expression "set ? 1 : 0" defined on "dom".
 */
static __isl_give isl_pw_aff *indicator_function(__isl_take isl_set *set,
	__isl_take isl_set *dom)
{
	isl_pw_aff *pa;
	pa = isl_set_indicator_function(set);
	pa = isl_pw_aff_intersect_domain(pa, isl_set_coalesce(dom));
	return pa;
}

/* Extract an affine expression from some binary operations.
 * If the result of the expression is unsigned, then we wrap it
 * based on the size of the type.  Otherwise, we ensure that
 * no overflow occurs.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(BinaryOperator *expr)
{
	isl_pw_aff *res;
	unsigned width;

	switch (expr->getOpcode()) {
	case BO_Add:
	case BO_Sub:
		res = extract_affine_add(expr);
		break;
	case BO_Div:
		res = extract_affine_div(expr);
		break;
	case BO_Rem:
		res = extract_affine_mod(expr);
		break;
	case BO_Mul:
		res = extract_affine_mul(expr);
		break;
	case BO_LT:
	case BO_LE:
	case BO_GT:
	case BO_GE:
	case BO_EQ:
	case BO_NE:
	case BO_LAnd:
	case BO_LOr:
		return extract_condition(expr);
	default:
		unsupported(expr);
		return NULL;
	}

	width = ast_context.getIntWidth(expr->getType());
	if (expr->getType()->isUnsignedIntegerType())
		res = wrap(res, width);
	else
		res = signed_overflow(res, width);

	return res;
}

/* Extract an affine expression from a negation operation.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(UnaryOperator *expr)
{
	if (expr->getOpcode() == UO_Minus)
		return isl_pw_aff_neg(extract_affine(expr->getSubExpr()));
	if (expr->getOpcode() == UO_LNot)
		return extract_condition(expr);

	unsupported(expr);
	return NULL;
}

__isl_give isl_pw_aff *PetScan::extract_affine(ParenExpr *expr)
{
	return extract_affine(expr->getSubExpr());
}

/* Extract an affine expression from some special function calls.
 * In particular, we handle "min", "max", "ceild", "floord",
 * "intMod", "intFloor" and "intCeil".
 * In case of the latter five, the second argument needs to be
 * a (positive) integer constant.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(CallExpr *expr)
{
	FunctionDecl *fd;
	string name;
	isl_pw_aff *aff1, *aff2;

	fd = expr->getDirectCallee();
	if (!fd) {
		unsupported(expr);
		return NULL;
	}

	name = fd->getDeclName().getAsString();
	if (!(expr->getNumArgs() == 2 && name == "min") &&
	    !(expr->getNumArgs() == 2 && name == "max") &&
	    !(expr->getNumArgs() == 2 && name == "intMod") &&
	    !(expr->getNumArgs() == 2 && name == "intFloor") &&
	    !(expr->getNumArgs() == 2 && name == "intCeil") &&
	    !(expr->getNumArgs() == 2 && name == "floord") &&
	    !(expr->getNumArgs() == 2 && name == "ceild")) {
		unsupported(expr);
		return NULL;
	}

	if (name == "min" || name == "max") {
		aff1 = extract_affine(expr->getArg(0));
		aff2 = extract_affine(expr->getArg(1));

		if (name == "min")
			aff1 = isl_pw_aff_min(aff1, aff2);
		else
			aff1 = isl_pw_aff_max(aff1, aff2);
	} else if (name == "intMod") {
		isl_val *v;
		Expr *arg2 = expr->getArg(1);

		if (arg2->getStmtClass() != Stmt::IntegerLiteralClass) {
			unsupported(expr);
			return NULL;
		}
		aff1 = extract_affine(expr->getArg(0));
		v = extract_int(cast<IntegerLiteral>(arg2));
		aff1 = isl_pw_aff_mod_val(aff1, v);
	} else if (name == "floord" || name == "ceild" ||
		   name == "intFloor" || name == "intCeil") {
		isl_val *v;
		Expr *arg2 = expr->getArg(1);

		if (arg2->getStmtClass() != Stmt::IntegerLiteralClass) {
			unsupported(expr);
			return NULL;
		}
		aff1 = extract_affine(expr->getArg(0));
		v = extract_int(cast<IntegerLiteral>(arg2));
		aff1 = isl_pw_aff_scale_down_val(aff1, v);
		if (name == "floord" || name == "intFloor")
			aff1 = isl_pw_aff_floor(aff1);
		else
			aff1 = isl_pw_aff_ceil(aff1);
	} else {
		unsupported(expr);
		return NULL;
	}

	return aff1;
}

/* This method is called when we come across an access that is
 * nested in what is supposed to be an affine expression.
 * If nesting is allowed, we return a new parameter that corresponds
 * to this nested access.  Otherwise, we simply complain.
 *
 * Note that we currently don't allow nested accesses themselves
 * to contain any nested accesses, so we check if we can extract
 * the access without any nesting and complain if we can't.
 *
 * The new parameter is resolved in resolve_nested.
 */
isl_pw_aff *PetScan::nested_access(Expr *expr)
{
	isl_id *id;
	isl_space *dim;
	isl_aff *aff;
	isl_set *dom;
	isl_multi_pw_aff *index;

	if (!nesting_enabled) {
		unsupported(expr);
		return NULL;
	}

	allow_nested = false;
	index = extract_index(expr);
	allow_nested = true;
	if (!index) {
		unsupported(expr);
		return NULL;
	}
	isl_multi_pw_aff_free(index);

	id = pet_nested_clang_expr(ctx, expr);
	dim = isl_space_params_alloc(ctx, 1);

	dim = isl_space_set_dim_id(dim, isl_dim_param, 0, id);

	dom = isl_set_universe(isl_space_copy(dim));
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient_si(aff, isl_dim_param, 0, 1);

	return isl_pw_aff_alloc(dom, aff);
}

/* Affine expressions are not supposed to contain array accesses,
 * but if nesting is allowed, we return a parameter corresponding
 * to the array access.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(ArraySubscriptExpr *expr)
{
	return nested_access(expr);
}

/* Affine expressions are not supposed to contain member accesses,
 * but if nesting is allowed, we return a parameter corresponding
 * to the member access.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(MemberExpr *expr)
{
	return nested_access(expr);
}

/* Extract an affine expression from a conditional operation.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(ConditionalOperator *expr)
{
	isl_pw_aff *cond, *lhs, *rhs;

	cond = extract_condition(expr->getCond());
	lhs = extract_affine(expr->getTrueExpr());
	rhs = extract_affine(expr->getFalseExpr());

	return isl_pw_aff_cond(cond, lhs, rhs);
}

/* Extract an affine expression, if possible, from "expr".
 * Otherwise return NULL.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(Expr *expr)
{
	switch (expr->getStmtClass()) {
	case Stmt::ImplicitCastExprClass:
		return extract_affine(cast<ImplicitCastExpr>(expr));
	case Stmt::IntegerLiteralClass:
		return extract_affine(cast<IntegerLiteral>(expr));
	case Stmt::DeclRefExprClass:
		return extract_affine(cast<DeclRefExpr>(expr));
	case Stmt::BinaryOperatorClass:
		return extract_affine(cast<BinaryOperator>(expr));
	case Stmt::UnaryOperatorClass:
		return extract_affine(cast<UnaryOperator>(expr));
	case Stmt::ParenExprClass:
		return extract_affine(cast<ParenExpr>(expr));
	case Stmt::CallExprClass:
		return extract_affine(cast<CallExpr>(expr));
	case Stmt::ArraySubscriptExprClass:
		return extract_affine(cast<ArraySubscriptExpr>(expr));
	case Stmt::MemberExprClass:
		return extract_affine(cast<MemberExpr>(expr));
	case Stmt::ConditionalOperatorClass:
		return extract_affine(cast<ConditionalOperator>(expr));
	default:
		unsupported(expr);
	}
	return NULL;
}

__isl_give isl_multi_pw_aff *PetScan::extract_index(ImplicitCastExpr *expr)
{
	return extract_index(expr->getSubExpr());
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

/* Extract an index expression from a reference to a variable.
 * If the variable has name "A", then the returned index expression
 * is of the form
 *
 *	{ [] -> A[] }
 */
__isl_give isl_multi_pw_aff *PetScan::extract_index(DeclRefExpr *expr)
{
	return extract_index(expr->getDecl());
}

/* Extract an index expression from a variable.
 * If the variable has name "A", then the returned index expression
 * is of the form
 *
 *	{ [] -> A[] }
 */
__isl_give isl_multi_pw_aff *PetScan::extract_index(ValueDecl *decl)
{
	isl_id *id = isl_id_alloc(ctx, decl->getName().str().c_str(), decl);
	isl_space *space = isl_space_alloc(ctx, 0, 0, 0);

	space = isl_space_set_tuple_id(space, isl_dim_out, id);

	return isl_multi_pw_aff_zero(space);
}

/* Extract an index expression from an integer contant.
 * If the value of the constant is "v", then the returned access relation
 * is
 *
 *	{ [] -> [v] }
 */
__isl_give isl_multi_pw_aff *PetScan::extract_index(IntegerLiteral *expr)
{
	isl_multi_pw_aff *mpa;

	mpa = isl_multi_pw_aff_from_pw_aff(extract_affine(expr));
	mpa = isl_multi_pw_aff_from_range(mpa);
	return mpa;
}

/* Try and extract an index expression from the given Expr.
 * Return NULL if it doesn't work out.
 */
__isl_give isl_multi_pw_aff *PetScan::extract_index(Expr *expr)
{
	switch (expr->getStmtClass()) {
	case Stmt::ImplicitCastExprClass:
		return extract_index(cast<ImplicitCastExpr>(expr));
	case Stmt::DeclRefExprClass:
		return extract_index(cast<DeclRefExpr>(expr));
	case Stmt::ArraySubscriptExprClass:
		return extract_index(cast<ArraySubscriptExpr>(expr));
	case Stmt::IntegerLiteralClass:
		return extract_index(cast<IntegerLiteral>(expr));
	case Stmt::MemberExprClass:
		return extract_index(cast<MemberExpr>(expr));
	default:
		unsupported(expr);
	}
	return NULL;
}

/* Given a partial index expression "base" and an extra index "index",
 * append the extra index to "base" and return the result.
 * Additionally, add the constraints that the extra index is non-negative.
 * If "index" represent a member access, i.e., if its range is a wrapped
 * relation, then we recursively extend the range of this nested relation.
 */
static __isl_give isl_multi_pw_aff *subscript(__isl_take isl_multi_pw_aff *base,
	__isl_take isl_pw_aff *index)
{
	isl_id *id;
	isl_set *domain;
	isl_multi_pw_aff *access;
	int member_access;

	member_access = isl_multi_pw_aff_range_is_wrapping(base);
	if (member_access < 0)
		goto error;
	if (member_access) {
		isl_multi_pw_aff *domain, *range;
		isl_id *id;

		id = isl_multi_pw_aff_get_tuple_id(base, isl_dim_out);
		domain = isl_multi_pw_aff_copy(base);
		domain = isl_multi_pw_aff_range_factor_domain(domain);
		range = isl_multi_pw_aff_range_factor_range(base);
		range = subscript(range, index);
		access = isl_multi_pw_aff_range_product(domain, range);
		access = isl_multi_pw_aff_set_tuple_id(access, isl_dim_out, id);
		return access;
	}

	id = isl_multi_pw_aff_get_tuple_id(base, isl_dim_set);
	index = isl_pw_aff_from_range(index);
	domain = isl_pw_aff_nonneg_set(isl_pw_aff_copy(index));
	index = isl_pw_aff_intersect_domain(index, domain);
	access = isl_multi_pw_aff_from_pw_aff(index);
	access = isl_multi_pw_aff_flat_range_product(base, access);
	access = isl_multi_pw_aff_set_tuple_id(access, isl_dim_set, id);

	return access;
error:
	isl_multi_pw_aff_free(base);
	isl_pw_aff_free(index);
	return NULL;
}

/* Extract an index expression from the given array subscript expression.
 * If nesting is allowed in general, then we turn it on while
 * examining the index expression.
 *
 * We first extract an index expression from the base.
 * This will result in an index expression with a range that corresponds
 * to the earlier indices.
 * We then extract the current index, restrict its domain
 * to those values that result in a non-negative index and
 * append the index to the base index expression.
 */
__isl_give isl_multi_pw_aff *PetScan::extract_index(ArraySubscriptExpr *expr)
{
	Expr *base = expr->getBase();
	Expr *idx = expr->getIdx();
	isl_pw_aff *index;
	isl_multi_pw_aff *base_access;
	isl_multi_pw_aff *access;
	bool save_nesting = nesting_enabled;

	nesting_enabled = allow_nested;

	base_access = extract_index(base);
	index = extract_affine(idx);

	nesting_enabled = save_nesting;

	access = subscript(base_access, index);

	return access;
}

/* Construct a name for a member access by concatenating the name
 * of the array of structures and the member, separated by an underscore.
 *
 * The caller is responsible for freeing the result.
 */
static char *member_access_name(isl_ctx *ctx, const char *base,
	const char *field)
{
	int len;
	char *name;

	len = strlen(base) + 1 + strlen(field);
	name = isl_alloc_array(ctx, char, len + 1);
	if (!name)
		return NULL;
	snprintf(name, len + 1, "%s_%s", base, field);

	return name;
}

/* Given an index expression "base" for an element of an array of structures
 * and an expression "field" for the field member being accessed, construct
 * an index expression for an access to that member of the given structure.
 * In particular, take the range product of "base" and "field" and
 * attach a name to the result.
 */
static __isl_give isl_multi_pw_aff *member(__isl_take isl_multi_pw_aff *base,
	__isl_take isl_multi_pw_aff *field)
{
	isl_ctx *ctx;
	isl_multi_pw_aff *access;
	const char *base_name, *field_name;
	char *name;

	ctx = isl_multi_pw_aff_get_ctx(base);

	base_name = isl_multi_pw_aff_get_tuple_name(base, isl_dim_out);
	field_name = isl_multi_pw_aff_get_tuple_name(field, isl_dim_out);
	name = member_access_name(ctx, base_name, field_name);

	access = isl_multi_pw_aff_range_product(base, field);

	access = isl_multi_pw_aff_set_tuple_name(access, isl_dim_out, name);
	free(name);

	return access;
}

/* Extract an index expression from a member expression.
 *
 * If the base access (to the structure containing the member)
 * is of the form
 *
 *	[] -> A[..]
 *
 * and the member is called "f", then the member access is of
 * the form
 *
 *	[] -> A_f[A[..] -> f[]]
 *
 * If the member access is to an anonymous struct, then simply return
 *
 *	[] -> A[..]
 *
 * If the member access in the source code is of the form
 *
 *	A->f
 *
 * then it is treated as
 *
 *	A[0].f
 */
__isl_give isl_multi_pw_aff *PetScan::extract_index(MemberExpr *expr)
{
	Expr *base = expr->getBase();
	FieldDecl *field = cast<FieldDecl>(expr->getMemberDecl());
	isl_multi_pw_aff *base_access, *field_access;
	isl_id *id;
	isl_space *space;

	base_access = extract_index(base);

	if (expr->isArrow()) {
		isl_space *space = isl_space_params_alloc(ctx, 0);
		isl_local_space *ls = isl_local_space_from_space(space);
		isl_aff *aff = isl_aff_zero_on_domain(ls);
		isl_pw_aff *index = isl_pw_aff_from_aff(aff);
		base_access = subscript(base_access, index);
	}

	if (field->isAnonymousStructOrUnion())
		return base_access;

	id = isl_id_alloc(ctx, field->getName().str().c_str(), field);
	space = isl_multi_pw_aff_get_domain_space(base_access);
	space = isl_space_from_domain(space);
	space = isl_space_set_tuple_id(space, isl_dim_out, id);
	field_access = isl_multi_pw_aff_zero(space);

	return member(base_access, field_access);
}

/* Check if "expr" calls function "minmax" with two arguments and if so
 * make lhs and rhs refer to these two arguments.
 */
static bool is_minmax(Expr *expr, const char *minmax, Expr *&lhs, Expr *&rhs)
{
	CallExpr *call;
	FunctionDecl *fd;
	string name;

	if (expr->getStmtClass() != Stmt::CallExprClass)
		return false;

	call = cast<CallExpr>(expr);
	fd = call->getDirectCallee();
	if (!fd)
		return false;

	if (call->getNumArgs() != 2)
		return false;

	name = fd->getDeclName().getAsString();
	if (name != minmax)
		return false;

	lhs = call->getArg(0);
	rhs = call->getArg(1);

	return true;
}

/* Check if "expr" is of the form min(lhs, rhs) and if so make
 * lhs and rhs refer to the two arguments.
 */
static bool is_min(Expr *expr, Expr *&lhs, Expr *&rhs)
{
	return is_minmax(expr, "min", lhs, rhs);
}

/* Check if "expr" is of the form max(lhs, rhs) and if so make
 * lhs and rhs refer to the two arguments.
 */
static bool is_max(Expr *expr, Expr *&lhs, Expr *&rhs)
{
	return is_minmax(expr, "max", lhs, rhs);
}

/* Extract an affine expressions representing the comparison "LHS op RHS"
 * "comp" is the original statement that "LHS op RHS" is derived from
 * and is used for diagnostics.
 *
 * If the comparison is of the form
 *
 *	a <= min(b,c)
 *
 * then the expression is constructed as the conjunction of
 * the comparisons
 *
 *	a <= b		and		a <= c
 *
 * A similar optimization is performed for max(a,b) <= c.
 * We do this because that will lead to simpler representations
 * of the expression.
 * If isl is ever enhanced to explicitly deal with min and max expressions,
 * this optimization can be removed.
 */
__isl_give isl_pw_aff *PetScan::extract_comparison(BinaryOperatorKind op,
	Expr *LHS, Expr *RHS, Stmt *comp)
{
	isl_pw_aff *lhs;
	isl_pw_aff *rhs;
	isl_pw_aff *res;
	isl_set *cond;
	isl_set *dom;
	enum pet_op_type type;

	if (op == BO_GT)
		return extract_comparison(BO_LT, RHS, LHS, comp);
	if (op == BO_GE)
		return extract_comparison(BO_LE, RHS, LHS, comp);

	if (op == BO_LT || op == BO_LE) {
		Expr *expr1, *expr2;
		if (is_min(RHS, expr1, expr2)) {
			lhs = extract_comparison(op, LHS, expr1, comp);
			rhs = extract_comparison(op, LHS, expr2, comp);
			return pet_and(lhs, rhs);
		}
		if (is_max(LHS, expr1, expr2)) {
			lhs = extract_comparison(op, expr1, RHS, comp);
			rhs = extract_comparison(op, expr2, RHS, comp);
			return pet_and(lhs, rhs);
		}
	}

	lhs = extract_affine(LHS);
	rhs = extract_affine(RHS);

	type = BinaryOperatorKind2pet_op_type(op);
	return pet_comparison(type, lhs, rhs);
}

__isl_give isl_pw_aff *PetScan::extract_comparison(BinaryOperator *comp)
{
	return extract_comparison(comp->getOpcode(), comp->getLHS(),
				comp->getRHS(), comp);
}

/* Extract an affine expression representing the negation (logical not)
 * of a subexpression.
 */
__isl_give isl_pw_aff *PetScan::extract_boolean(UnaryOperator *op)
{
	isl_pw_aff *cond;

	cond = extract_condition(op->getSubExpr());
	return pet_not(cond);
}

/* Extract an affine expression representing the disjunction (logical or)
 * or conjunction (logical and) of two subexpressions.
 */
__isl_give isl_pw_aff *PetScan::extract_boolean(BinaryOperator *comp)
{
	isl_pw_aff *lhs, *rhs;

	lhs = extract_condition(comp->getLHS());
	rhs = extract_condition(comp->getRHS());

	switch (comp->getOpcode()) {
	case BO_LAnd:
		return pet_boolean(pet_op_land, lhs, rhs);
	case BO_LOr:
		return pet_boolean(pet_op_lor, lhs, rhs);
	default:
		isl_pw_aff_free(lhs);
		isl_pw_aff_free(rhs);
	}

	unsupported(comp);
	return NULL;
}

__isl_give isl_pw_aff *PetScan::extract_condition(UnaryOperator *expr)
{
	switch (expr->getOpcode()) {
	case UO_LNot:
		return extract_boolean(expr);
	default:
		unsupported(expr);
		return NULL;
	}
}

/* Extract the affine expression "expr != 0 ? 1 : 0".
 */
__isl_give isl_pw_aff *PetScan::extract_implicit_condition(Expr *expr)
{
	isl_pw_aff *res;

	res = extract_affine(expr);
	return pet_to_bool(res);
}

/* Extract an affine expression from a boolean expression.
 * In particular, return the expression "expr ? 1 : 0".
 *
 * If the expression doesn't look like a condition, we assume it
 * is an affine expression and return the condition "expr != 0 ? 1 : 0".
 */
__isl_give isl_pw_aff *PetScan::extract_condition(Expr *expr)
{
	BinaryOperator *comp;

	if (!expr) {
		isl_set *u = isl_set_universe(isl_space_params_alloc(ctx, 0));
		return indicator_function(u, isl_set_copy(u));
	}

	if (expr->getStmtClass() == Stmt::ParenExprClass)
		return extract_condition(cast<ParenExpr>(expr)->getSubExpr());

	if (expr->getStmtClass() == Stmt::UnaryOperatorClass)
		return extract_condition(cast<UnaryOperator>(expr));

	if (expr->getStmtClass() != Stmt::BinaryOperatorClass)
		return extract_implicit_condition(expr);

	comp = cast<BinaryOperator>(expr);
	switch (comp->getOpcode()) {
	case BO_LT:
	case BO_LE:
	case BO_GT:
	case BO_GE:
	case BO_EQ:
	case BO_NE:
		return extract_comparison(comp);
	case BO_LAnd:
	case BO_LOr:
		return extract_boolean(comp);
	default:
		return extract_implicit_condition(expr);
	}
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

/* Mark the given access pet_expr as a write.
 * If a scalar is being accessed, then mark its value
 * as unknown in assigned_value.
 */
__isl_give pet_expr *PetScan::mark_write(__isl_take pet_expr *access)
{
	isl_id *id;
	ValueDecl *decl;

	access = pet_expr_access_set_write(access, 1);
	access = pet_expr_access_set_read(access, 0);

	if (!access || !pet_expr_is_scalar_access(access))
		return access;

	id = pet_expr_access_get_id(access);
	decl = (ValueDecl *) isl_id_get_user(id);
	clear_assignment(assigned_value, decl);
	isl_id_free(id);

	return access;
}

/* Assign "rhs" to "lhs".
 *
 * In particular, if "lhs" is a scalar variable, then mark
 * the variable as having been assigned.  If, furthermore, "rhs"
 * is an affine expression, then keep track of this value in assigned_value
 * so that we can plug it in when we later come across the same variable.
 */
void PetScan::assign(__isl_keep pet_expr *lhs, Expr *rhs)
{
	isl_id *id;
	ValueDecl *decl;
	isl_pw_aff *pa;

	if (!lhs)
		return;
	if (!pet_expr_is_scalar_access(lhs))
		return;

	id = pet_expr_access_get_id(lhs);
	decl = (ValueDecl *) isl_id_get_user(id);
	isl_id_free(id);

	pa = try_extract_affine(rhs);
	clear_assignment(assigned_value, decl);
	if (!pa)
		return;
	assigned_value[decl] = pa;
	insert_expression(pa);
}

/* Construct a pet_expr representing a binary operator expression.
 *
 * If the top level operator is an assignment and the LHS is an access,
 * then we mark that access as a write.  If the operator is a compound
 * assignment, the access is marked as both a read and a write.
 *
 * If "expr" assigns something to a scalar variable, then we mark
 * the variable as having been assigned.  If, furthermore, the expression
 * is affine, then keep track of this value in assigned_value
 * so that we can plug it in when we later come across the same variable.
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

	if (expr->getOpcode() == BO_Assign)
		assign(lhs, expr->getRHS());

	type_size = get_type_size(expr->getType(), ast_context);
	return pet_expr_new_binary(type_size, op, lhs, rhs);
}

/* Construct a pet_scop with a single statement killing the entire
 * array "array".
 */
struct pet_scop *PetScan::kill(Stmt *stmt, struct pet_array *array)
{
	isl_id *id;
	isl_space *space;
	isl_multi_pw_aff *index;
	isl_map *access;
	pet_expr *expr;

	if (!array)
		return NULL;
	access = isl_map_from_range(isl_set_copy(array->extent));
	id = isl_set_get_tuple_id(array->extent);
	space = isl_space_alloc(ctx, 0, 0, 0);
	space = isl_space_set_tuple_id(space, isl_dim_out, id);
	index = isl_multi_pw_aff_zero(space);
	expr = pet_expr_kill_from_access_and_index(access, index);
	return extract(stmt, expr);
}

/* Construct a pet_scop for a (single) variable declaration.
 *
 * The scop contains the variable being declared (as an array)
 * and a statement killing the array.
 *
 * If the variable is initialized in the AST, then the scop
 * also contains an assignment to the variable.
 */
struct pet_scop *PetScan::extract(DeclStmt *stmt)
{
	int type_size;
	Decl *decl;
	VarDecl *vd;
	pet_expr *lhs, *rhs, *pe;
	struct pet_scop *scop_decl, *scop;
	struct pet_array *array;

	if (!stmt->isSingleDecl()) {
		unsupported(stmt);
		return NULL;
	}

	decl = stmt->getSingleDecl();
	vd = cast<VarDecl>(decl);

	array = extract_array(ctx, vd, NULL);
	if (array)
		array->declared = 1;
	scop_decl = kill(stmt, array);
	scop_decl = pet_scop_add_array(scop_decl, array);

	if (!vd->getInit())
		return scop_decl;

	lhs = extract_access_expr(vd);
	rhs = extract_expr(vd->getInit());

	lhs = mark_write(lhs);
	assign(lhs, vd->getInit());

	type_size = get_type_size(vd->getType(), ast_context);
	pe = pet_expr_new_binary(type_size, pet_op_assign, lhs, rhs);
	scop = extract(stmt, pe);

	scop_decl = pet_scop_prefix(scop_decl, 0);
	scop = pet_scop_prefix(scop, 1);

	scop = pet_scop_add_seq(ctx, scop_decl, scop);

	return scop;
}

/* Construct a pet_expr representing a conditional operation.
 *
 * We first try to extract the condition as an affine expression.
 * If that fails, we construct a pet_expr tree representing the condition.
 */
__isl_give pet_expr *PetScan::extract_expr(ConditionalOperator *expr)
{
	pet_expr *cond, *lhs, *rhs;
	isl_pw_aff *pa;

	pa = try_extract_affine(expr->getCond());
	if (pa) {
		isl_multi_pw_aff *test = isl_multi_pw_aff_from_pw_aff(pa);
		test = isl_multi_pw_aff_from_range(test);
		cond = pet_expr_from_index(test);
	} else
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
	__isl_take isl_multi_pw_aff *index)
{
	pet_expr *pe;
	int depth;
	int type_size;

	depth = extract_depth(index);
	type_size = get_type_size(qt, ast_context);

	pe = pet_expr_from_index_and_depth(type_size, index, depth);

	return pe;
}

/* Extract an index expression from "expr" and then convert it into
 * an access pet_expr.
 */
__isl_give pet_expr *PetScan::extract_access_expr(Expr *expr)
{
	return extract_access_expr(expr->getType(), extract_index(expr));
}

/* Extract an index expression from "decl" and then convert it into
 * an access pet_expr.
 */
__isl_give pet_expr *PetScan::extract_access_expr(ValueDecl *decl)
{
	return extract_access_expr(decl->getType(), extract_index(decl));
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
	isl_pw_aff *cond;
	pet_expr *res;

	cond = try_extract_affine_condition(expr);
	if (!cond) {
		res = extract_expr(expr);
	} else {
		isl_multi_pw_aff *index;
		index = isl_multi_pw_aff_from_pw_aff(cond);
		index = isl_multi_pw_aff_from_range(index);
		res = pet_expr_from_index(index);
	}
	return pet_expr_new_unary(pet_op_assume, res);
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
 * Return an affine expression "1" or "-1" accordingly.
 */
__isl_give isl_pw_aff *PetScan::extract_unary_increment(
	clang::UnaryOperator *op, clang::ValueDecl *iv)
{
	Expr *sub;
	DeclRefExpr *ref;
	isl_space *space;
	isl_aff *aff;

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

	space = isl_space_params_alloc(ctx, 0);
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(space));

	if (op->isIncrementOp())
		aff = isl_aff_add_constant_si(aff, 1);
	else
		aff = isl_aff_add_constant_si(aff, -1);

	return isl_pw_aff_from_aff(aff);
}

/* Check if op is of the form
 *
 *	iv = iv + inc
 *
 * and return inc as an affine expression.
 *
 * We extract an affine expression from the RHS, subtract iv and return
 * the result.
 */
__isl_give isl_pw_aff *PetScan::extract_binary_increment(BinaryOperator *op,
	clang::ValueDecl *iv)
{
	Expr *lhs;
	DeclRefExpr *ref;
	isl_id *id;
	isl_space *dim;
	isl_aff *aff;
	isl_pw_aff *val;

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

	val = extract_affine(op->getRHS());

	id = isl_id_alloc(ctx, iv->getName().str().c_str(), iv);

	dim = isl_space_params_alloc(ctx, 1);
	dim = isl_space_set_dim_id(dim, isl_dim_param, 0, id);
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient_si(aff, isl_dim_param, 0, 1);

	val = isl_pw_aff_sub(val, isl_pw_aff_from_aff(aff));

	return val;
}

/* Check that op is of the form iv += cst or iv -= cst
 * and return an affine expression corresponding oto cst or -cst accordingly.
 */
__isl_give isl_pw_aff *PetScan::extract_compound_increment(
	CompoundAssignOperator *op, clang::ValueDecl *iv)
{
	Expr *lhs;
	DeclRefExpr *ref;
	bool neg = false;
	isl_pw_aff *val;
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

	val = extract_affine(op->getRHS());
	if (neg)
		val = isl_pw_aff_neg(val);

	return val;
}

/* Check that the increment of the given for loop increments
 * (or decrements) the induction variable "iv" and return
 * the increment as an affine expression if successful.
 */
__isl_give isl_pw_aff *PetScan::extract_increment(clang::ForStmt *stmt,
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

/* Construct a pet_scop for an infinite loop around the given body.
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
 *
 * If we were only able to extract part of the body, then simply
 * return that part.
 */
struct pet_scop *PetScan::extract_infinite_loop(Stmt *body)
{
	isl_id *id, *id_test;
	isl_set *domain;
	isl_aff *ident;
	struct pet_scop *scop;
	bool has_var_break;

	scop = extract(body);
	if (!scop)
		return NULL;
	if (partial)
		return scop;

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
 */
struct pet_scop *PetScan::extract_infinite_for(ForStmt *stmt)
{
	clear_assignments clear(assigned_value);
	clear.TraverseStmt(stmt->getBody());

	return extract_infinite_loop(stmt->getBody());
}

/* Add an array with the given extent (range of "index") to the list
 * of arrays in "scop" and return the extended pet_scop.
 * The array is marked as attaining values 0 and 1 only and
 * as each element being assigned at most once.
 */
static struct pet_scop *scop_add_array(struct pet_scop *scop,
	__isl_keep isl_multi_pw_aff *index, clang::ASTContext &ast_ctx)
{
	int int_size = ast_ctx.getTypeInfo(ast_ctx.IntTy).first / 8;

	return pet_scop_add_boolean_array(scop, isl_multi_pw_aff_copy(index),
						int_size);
}

/* Construct a pet_scop for a while loop of the form
 *
 *	while (pa)
 *		body
 *
 * In particular, construct a scop for an infinite loop around body and
 * intersect the domain with the affine expression.
 * Note that this intersection may result in an empty loop.
 */
struct pet_scop *PetScan::extract_affine_while(__isl_take isl_pw_aff *pa,
	Stmt *body)
{
	struct pet_scop *scop;
	isl_set *dom;
	isl_set *valid;

	valid = isl_pw_aff_domain(isl_pw_aff_copy(pa));
	dom = isl_pw_aff_non_zero_set(pa);
	scop = extract_infinite_loop(body);
	scop = pet_scop_restrict(scop, dom);
	scop = pet_scop_restrict_context(scop, valid);

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

/* Check if the while loop is of the form
 *
 *	while (affine expression)
 *		body
 *
 * If so, call extract_affine_while to construct a scop.
 *
 * Otherwise, construct a generic while scop, with iteration domain
 * { [t] : t >= 0 }.  The scop consists of two parts, one for
 * evaluating the condition and one for the body.
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
 *
 * If we were only able to extract part of the body, then simply
 * return that part.
 */
struct pet_scop *PetScan::extract(WhileStmt *stmt)
{
	Expr *cond;
	int test_nr, stmt_nr;
	isl_id *id, *id_test, *id_break_test;
	isl_multi_pw_aff *test_index;
	isl_set *domain;
	isl_aff *ident;
	isl_pw_aff *pa;
	struct pet_scop *scop, *scop_body;
	bool has_var_break;

	cond = stmt->getCond();
	if (!cond) {
		unsupported(stmt);
		return NULL;
	}

	clear_assignments clear(assigned_value);
	clear.TraverseStmt(stmt->getBody());

	pa = try_extract_affine_condition(cond);
	if (pa)
		return extract_affine_while(pa, stmt->getBody());

	if (!allow_nested) {
		unsupported(stmt);
		return NULL;
	}

	test_nr = n_test++;
	stmt_nr = n_stmt++;
	scop_body = extract(stmt->getBody());
	if (partial)
		return scop_body;

	test_index = pet_create_test_index(ctx, test_nr);
	scop = extract_non_affine_condition(cond, stmt_nr,
					    isl_multi_pw_aff_copy(test_index));
	scop = scop_add_array(scop, test_index, ast_context);
	id_test = isl_multi_pw_aff_get_tuple_id(test_index, isl_dim_out);
	isl_multi_pw_aff_free(test_index);

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

	return scop;
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
static bool can_wrap(__isl_keep isl_set *cond, ValueDecl *iv,
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
		limit = isl_val_int_from_ui(ctx, get_type_size(iv));
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
	ValueDecl *iv)
{
	isl_ctx *ctx;
	isl_val *mod;
	isl_aff *aff;

	ctx = isl_space_get_ctx(dim);
	mod = isl_val_int_from_ui(ctx, get_type_size(iv));
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

/* Construct a pet_scop for a for statement.
 * The for loop is required to be of the form
 *
 *	for (i = init; condition; ++i)
 *
 * or
 *
 *	for (i = init; condition; --i)
 *
 * The initialization of the for loop should either be an assignment
 * to an integer variable, or a declaration of such a variable with
 * initialization.
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
 * Before extracting a pet_scop from the body we remove all
 * assignments in assigned_value to variables that are assigned
 * somewhere in the body of the loop.
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
 *
 * If we were only able to extract part of the body, then simply
 * return that part.
 */
struct pet_scop *PetScan::extract_for(ForStmt *stmt)
{
	BinaryOperator *ass;
	Decl *decl;
	Stmt *init;
	Expr *lhs, *rhs;
	ValueDecl *iv;
	isl_local_space *ls;
	isl_set *domain;
	isl_aff *sched;
	isl_set *cond = NULL;
	isl_set *skip = NULL;
	isl_id *id, *id_test = NULL, *id_break_test;
	struct pet_scop *scop, *scop_cond = NULL;
	assigned_value_cache cache(assigned_value);
	isl_val *inc;
	bool was_assigned;
	bool is_one;
	bool is_unsigned;
	bool is_simple;
	bool is_virtual;
	bool has_affine_break;
	bool has_var_break;
	isl_aff *wrap = NULL;
	isl_pw_aff *pa, *pa_inc, *init_val;
	isl_set *valid_init;
	isl_set *valid_cond;
	isl_set *valid_cond_init;
	isl_set *valid_cond_next;
	isl_set *valid_inc;
	int stmt_id;

	if (!stmt->getInit() && !stmt->getCond() && !stmt->getInc())
		return extract_infinite_for(stmt);

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

	assigned_value.erase(iv);
	clear_assignments clear(assigned_value);
	clear.TraverseStmt(stmt->getBody());

	was_assigned = assigned_value.find(iv) != assigned_value.end();
	clear_assignment(assigned_value, iv);
	init_val = extract_affine(rhs);
	if (!was_assigned)
		assigned_value.erase(iv);
	if (!init_val)
		return NULL;

	pa_inc = extract_increment(stmt, iv);
	if (!pa_inc) {
		isl_pw_aff_free(init_val);
		return NULL;
	}

	inc = pet_extract_cst(pa_inc);
	if (!inc || isl_val_is_nan(inc)) {
		isl_pw_aff_free(init_val);
		isl_pw_aff_free(pa_inc);
		unsupported(stmt->getInc());
		isl_val_free(inc);
		return NULL;
	}

	pa = try_extract_nested_condition(stmt->getCond());
	if (allow_nested && (!pa || pet_nested_any_in_pw_aff(pa)))
		stmt_id = n_stmt++;

	scop = extract(stmt->getBody());
	if (partial) {
		isl_pw_aff_free(init_val);
		isl_pw_aff_free(pa_inc);
		isl_pw_aff_free(pa);
		isl_val_free(inc);
		return scop;
	}

	valid_inc = isl_pw_aff_domain(pa_inc);

	is_unsigned = iv->getType()->isUnsignedIntegerType();

	id = isl_id_alloc(ctx, iv->getName().str().c_str(), iv);

	has_affine_break = scop &&
				pet_scop_has_affine_skip(scop, pet_skip_later);
	if (has_affine_break)
		skip = pet_scop_get_affine_skip_domain(scop, pet_skip_later);
	has_var_break = scop && pet_scop_has_var_skip(scop, pet_skip_later);
	if (has_var_break)
		id_break_test = pet_scop_get_skip_id(scop, pet_skip_later);

	if (pa && !is_nested_allowed(pa, scop)) {
		isl_pw_aff_free(pa);
		pa = NULL;
	}

	if (!allow_nested && !pa)
		pa = try_extract_affine_condition(stmt->getCond());
	valid_cond = isl_pw_aff_domain(isl_pw_aff_copy(pa));
	cond = isl_pw_aff_non_zero_set(pa);
	if (allow_nested && !cond) {
		isl_multi_pw_aff *test_index;
		int save_n_stmt = n_stmt;
		test_index = pet_create_test_index(ctx, n_test++);
		n_stmt = stmt_id;
		scop_cond = extract_non_affine_condition(stmt->getCond(),
				n_stmt++, isl_multi_pw_aff_copy(test_index));
		n_stmt = save_n_stmt;
		scop_cond = scop_add_array(scop_cond, test_index, ast_context);
		id_test = isl_multi_pw_aff_get_tuple_id(test_index,
							isl_dim_out);
		isl_multi_pw_aff_free(test_index);
		scop_cond = pet_scop_prefix(scop_cond, 0);
		scop = pet_scop_reset_context(scop);
		scop = pet_scop_prefix(scop, 1);
		cond = isl_set_universe(isl_space_set_alloc(ctx, 0, 0));
	}

	cond = embed(cond, isl_id_copy(id));
	skip = embed(skip, isl_id_copy(id));
	valid_cond = isl_set_coalesce(valid_cond);
	valid_cond = embed(valid_cond, isl_id_copy(id));
	valid_inc = embed(valid_inc, isl_id_copy(id));
	is_one = isl_val_is_one(inc) || isl_val_is_negone(inc);
	is_virtual = is_unsigned && (!is_one || can_wrap(cond, iv, inc));

	valid_cond_init = enforce_subset(
		isl_set_from_pw_aff(isl_pw_aff_copy(init_val)),
		isl_set_copy(valid_cond));
	if (is_one && !is_virtual) {
		isl_pw_aff_free(init_val);
		pa = extract_comparison(isl_val_is_pos(inc) ? BO_GE : BO_LE,
				lhs, rhs, init);
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
		wrap = compute_wrapping(isl_set_get_space(cond), iv);
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
	scop = resolve_nested(scop);
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
	clear_assignment(assigned_value, iv);

	isl_val_free(inc);

	scop = pet_scop_restrict_context(scop, valid_init);

	return scop;
}

/* Try and construct a pet_scop corresponding to a compound statement.
 *
 * "skip_declarations" is set if we should skip initial declarations
 * in the children of the compound statements.  This then implies
 * that this sequence of children should not be treated as a block
 * since the initial statements may be skipped.
 */
struct pet_scop *PetScan::extract(CompoundStmt *stmt, bool skip_declarations)
{
	return extract(stmt->children(), !skip_declarations, skip_declarations);
}

/* Extract a pet_expr from an isl_id created by either pet_nested_clang_expr or
 * pet_nested_pet_expr.
 * In the first case, the isl_id has no name and
 * the user pointer points to a clang::Expr object.
 * In the second case, the isl_id has name "__pet_expr" and
 * the user pointer points to a pet_expr object.
 */
__isl_give pet_expr *PetScan::extract_expr(__isl_keep isl_id *id)
{
	if (!isl_id_get_name(id))
		return extract_expr((Expr *) isl_id_get_user(id));
	else
		return pet_expr_copy((pet_expr *) isl_id_get_user(id));
}

/* For each nested access parameter in "space",
 * construct a corresponding pet_expr, place it in args and
 * record its position in "param2pos".
 * "n_arg" is the number of elements that are already in args.
 * The position recorded in "param2pos" takes this number into account.
 * If the pet_expr corresponding to a parameter is identical to
 * the pet_expr corresponding to an earlier parameter, then these two
 * parameters are made to refer to the same element in args.
 *
 * Return the final number of elements in args or -1 if an error has occurred.
 */
int PetScan::extract_nested(__isl_keep isl_space *space,
	int n_arg, pet_expr **args, std::map<int,int> &param2pos)
{
	int nparam;

	nparam = isl_space_dim(space, isl_dim_param);
	for (int i = 0; i < nparam; ++i) {
		int j;
		isl_id *id = isl_space_get_dim_id(space, isl_dim_param, i);

		if (!pet_nested_in_id(id)) {
			isl_id_free(id);
			continue;
		}

		args[n_arg] = extract_expr(id);
		isl_id_free(id);
		if (!args[n_arg])
			return -1;

		for (j = 0; j < n_arg; ++j)
			if (pet_expr_is_equal(args[j], args[n_arg]))
				break;

		if (j < n_arg) {
			pet_expr_free(args[n_arg]);
			args[n_arg] = NULL;
			param2pos[i] = j;
		} else
			param2pos[i] = n_arg++;
	}

	return n_arg;
}

/* For each nested access parameter in the access relations in "expr",
 * construct a corresponding pet_expr, place it in the arguments of "expr"
 * and record its position in "param2pos".
 * n is the number of nested access parameters.
 */
__isl_give pet_expr *PetScan::extract_nested(__isl_take pet_expr *expr, int n,
	std::map<int,int> &param2pos)
{
	isl_space *space;
	int i;
	pet_expr **args;

	args = isl_calloc_array(ctx, pet_expr *, n);
	if (!args)
		return pet_expr_free(expr);

	space = pet_expr_access_get_parameter_space(expr);
	n = extract_nested(space, 0, args, param2pos);
	isl_space_free(space);

	if (n < 0)
		expr = pet_expr_free(expr);
	else
		expr = pet_expr_set_n_arg(expr, n);

	for (i = 0; i < n; ++i)
		expr = pet_expr_set_arg(expr, i, args[i]);
	free(args);

	return expr;
}

/* Look for parameters in any access relation in "expr" that
 * refer to nested accesses.  In particular, these are
 * parameters with either no name or with name "__pet_expr".
 *
 * If there are any such parameters, then the domain of the index
 * expression and the access relation, which is still [] at this point,
 * is replaced by [[] -> [t_1,...,t_n]], with n the number of these parameters
 * (after identifying identical nested accesses).
 *
 * This transformation is performed in several steps.
 * We first extract the arguments in extract_nested.
 * param2pos maps the original parameter position to the position
 * of the argument.
 * Then we move these parameters to input dimensions.
 * t2pos maps the positions of these temporary input dimensions
 * to the positions of the corresponding arguments.
 * Finally, we express these temporary dimensions in terms of the domain
 * [[] -> [t_1,...,t_n]] and precompose index expression and access
 * relations with this function.
 */
__isl_give pet_expr *PetScan::resolve_nested(__isl_take pet_expr *expr)
{
	int n;
	int nparam;
	isl_space *space;
	isl_local_space *ls;
	isl_aff *aff;
	isl_multi_aff *ma;
	std::map<int,int> param2pos;
	std::map<int,int> t2pos;

	if (!expr)
		return expr;

	n = pet_expr_get_n_arg(expr);
	for (int i = 0; i < n; ++i) {
		pet_expr *arg;
		arg = pet_expr_get_arg(expr, i);
		arg = resolve_nested(arg);
		expr = pet_expr_set_arg(expr, i, arg);
	}

	if (pet_expr_get_type(expr) != pet_expr_access)
		return expr;

	space = pet_expr_access_get_parameter_space(expr);
	n = pet_nested_n_in_space(space);
	isl_space_free(space);
	if (n == 0)
		return expr;

	expr = extract_nested(expr, n, param2pos);
	if (!expr)
		return NULL;

	expr = pet_expr_access_align_params(expr);
	if (!expr)
		return NULL;

	n = 0;
	space = pet_expr_access_get_parameter_space(expr);
	nparam = isl_space_dim(space, isl_dim_param);
	for (int i = nparam - 1; i >= 0; --i) {
		isl_id *id = isl_space_get_dim_id(space, isl_dim_param, i);
		if (!pet_nested_in_id(id)) {
			isl_id_free(id);
			continue;
		}

		expr = pet_expr_access_move_dims(expr,
					isl_dim_in, n, isl_dim_param, i, 1);
		t2pos[n] = param2pos[i];
		n++;

		isl_id_free(id);
	}
	isl_space_free(space);

	space = pet_expr_access_get_parameter_space(expr);
	space = isl_space_set_from_params(space);
	space = isl_space_add_dims(space, isl_dim_set,
					pet_expr_get_n_arg(expr));
	space = isl_space_wrap(isl_space_from_range(space));
	ls = isl_local_space_from_space(isl_space_copy(space));
	space = isl_space_from_domain(space);
	space = isl_space_add_dims(space, isl_dim_out, n);
	ma = isl_multi_aff_zero(space);

	for (int i = 0; i < n; ++i) {
		aff = isl_aff_var_on_domain(isl_local_space_copy(ls),
					    isl_dim_set, t2pos[i]);
		ma = isl_multi_aff_set_aff(ma, i, aff);
	}
	isl_local_space_free(ls);

	expr = pet_expr_access_pullback_multi_aff(expr, ma);

	return expr;
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

/* Update start and end of "scop" to include the region covered by "range".
 * If "skip_semi" is set, then we assume "range" is followed by
 * a semicolon and also include this semicolon.
 */
struct pet_scop *PetScan::update_scop_start_end(struct pet_scop *scop,
	SourceRange range, bool skip_semi)
{
	SourceLocation loc = range.getBegin();
	SourceManager &SM = PP.getSourceManager();
	const LangOptions &LO = PP.getLangOpts();
	unsigned start, end;

	loc = move_to_start_of_line_if_first_token(loc, SM, LO);
	start = getExpansionOffset(SM, loc);
	loc = range.getEnd();
	if (skip_semi)
		loc = location_after_semi(loc, SM, LO);
	else
		loc = PP.getLocForEndOfToken(loc);
	end = getExpansionOffset(SM, loc);

	scop = pet_scop_update_start_end(scop, start, end);
	return scop;
}

/* Convert a top-level pet_expr to a pet_scop with one statement.
 * This mainly involves resolving nested expression parameters
 * and setting the name of the iteration space.
 * The name is given by "label" if it is non-NULL.  Otherwise,
 * it is of the form S_<n_stmt>.
 * start and end of the pet_scop are derived from those of "stmt".
 * If "stmt" is an expression statement, then its range does not
 * include the semicolon, while it should be included in the pet_scop.
 */
struct pet_scop *PetScan::extract(Stmt *stmt, __isl_take pet_expr *expr,
	__isl_take isl_id *label)
{
	struct pet_stmt *ps;
	struct pet_scop *scop;
	SourceLocation loc = stmt->getLocStart();
	int line = PP.getSourceManager().getExpansionLineNumber(loc);
	bool skip_semi;

	expr = resolve_nested(expr);
	ps = pet_stmt_from_pet_expr(line, label, n_stmt++, expr);
	scop = pet_scop_from_pet_stmt(ctx, ps);

	skip_semi = isa<Expr>(stmt);
	scop = update_scop_start_end(scop, stmt->getSourceRange(), skip_semi);
	return scop;
}

/* Check if we can extract an affine expression from "expr".
 * Return the expressions as an isl_pw_aff if we can and NULL otherwise.
 * We turn on autodetection so that we won't generate any warnings
 * and turn off nesting, so that we won't accept any non-affine constructs.
 */
__isl_give isl_pw_aff *PetScan::try_extract_affine(Expr *expr)
{
	isl_pw_aff *pwaff;
	int save_autodetect = options->autodetect;
	bool save_nesting = nesting_enabled;

	options->autodetect = 1;
	nesting_enabled = false;

	pwaff = extract_affine(expr);

	options->autodetect = save_autodetect;
	nesting_enabled = save_nesting;

	return pwaff;
}

/* Check if we can extract an affine constraint from "expr".
 * Return the constraint as an isl_set if we can and NULL otherwise.
 * We turn on autodetection so that we won't generate any warnings
 * and turn off nesting, so that we won't accept any non-affine constructs.
 */
__isl_give isl_pw_aff *PetScan::try_extract_affine_condition(Expr *expr)
{
	isl_pw_aff *cond;
	int save_autodetect = options->autodetect;
	bool save_nesting = nesting_enabled;

	options->autodetect = 1;
	nesting_enabled = false;

	cond = extract_condition(expr);

	options->autodetect = save_autodetect;
	nesting_enabled = save_nesting;

	return cond;
}

/* Check whether "expr" is an affine constraint.
 */
bool PetScan::is_affine_condition(Expr *expr)
{
	isl_pw_aff *cond;

	cond = try_extract_affine_condition(expr);
	isl_pw_aff_free(cond);

	return cond != NULL;
}

/* Check if we can extract a condition from "expr".
 * Return the condition as an isl_pw_aff if we can and NULL otherwise.
 * If allow_nested is set, then the condition may involve parameters
 * corresponding to nested accesses.
 * We turn on autodetection so that we won't generate any warnings.
 */
__isl_give isl_pw_aff *PetScan::try_extract_nested_condition(Expr *expr)
{
	isl_pw_aff *cond;
	int save_autodetect = options->autodetect;
	bool save_nesting = nesting_enabled;

	options->autodetect = 1;
	nesting_enabled = allow_nested;
	cond = extract_condition(expr);

	options->autodetect = save_autodetect;
	nesting_enabled = save_nesting;

	return cond;
}

/* If the top-level expression of "stmt" is an assignment, then
 * return that assignment as a BinaryOperator.
 * Otherwise return NULL.
 */
static BinaryOperator *top_assignment_or_null(Stmt *stmt)
{
	BinaryOperator *ass;

	if (!stmt)
		return NULL;
	if (stmt->getStmtClass() != Stmt::BinaryOperatorClass)
		return NULL;

	ass = cast<BinaryOperator>(stmt);
	if(ass->getOpcode() != BO_Assign)
		return NULL;

	return ass;
}

/* Check if the given if statement is a conditional assignement
 * with a non-affine condition.  If so, construct a pet_scop
 * corresponding to this conditional assignment.  Otherwise return NULL.
 *
 * In particular we check if "stmt" is of the form
 *
 *	if (condition)
 *		a = f(...);
 *	else
 *		a = g(...);
 *
 * where a is some array or scalar access.
 * The constructed pet_scop then corresponds to the expression
 *
 *	a = condition ? f(...) : g(...)
 *
 * All access relations in f(...) are intersected with condition
 * while all access relation in g(...) are intersected with the complement.
 */
struct pet_scop *PetScan::extract_conditional_assignment(IfStmt *stmt)
{
	BinaryOperator *ass_then, *ass_else;
	isl_multi_pw_aff *write_then, *write_else;
	isl_set *cond, *comp;
	isl_multi_pw_aff *index;
	isl_pw_aff *pa;
	int equal;
	int type_size;
	pet_expr *pe_cond, *pe_then, *pe_else, *pe, *pe_write;
	bool save_nesting = nesting_enabled;

	if (!options->detect_conditional_assignment)
		return NULL;

	ass_then = top_assignment_or_null(stmt->getThen());
	ass_else = top_assignment_or_null(stmt->getElse());

	if (!ass_then || !ass_else)
		return NULL;

	if (is_affine_condition(stmt->getCond()))
		return NULL;

	write_then = extract_index(ass_then->getLHS());
	write_else = extract_index(ass_else->getLHS());

	equal = isl_multi_pw_aff_plain_is_equal(write_then, write_else);
	isl_multi_pw_aff_free(write_else);
	if (equal < 0 || !equal) {
		isl_multi_pw_aff_free(write_then);
		return NULL;
	}

	nesting_enabled = allow_nested;
	pa = extract_condition(stmt->getCond());
	nesting_enabled = save_nesting;
	cond = isl_pw_aff_non_zero_set(isl_pw_aff_copy(pa));
	comp = isl_pw_aff_zero_set(isl_pw_aff_copy(pa));
	index = isl_multi_pw_aff_from_range(isl_multi_pw_aff_from_pw_aff(pa));

	pe_cond = pet_expr_from_index(index);

	pe_then = extract_expr(ass_then->getRHS());
	pe_then = pet_expr_restrict(pe_then, cond);
	pe_else = extract_expr(ass_else->getRHS());
	pe_else = pet_expr_restrict(pe_else, comp);

	pe = pet_expr_new_ternary(pe_cond, pe_then, pe_else);
	type_size = get_type_size(ass_then->getType(), ast_context);
	pe_write = pet_expr_from_index_and_depth(type_size, write_then,
						extract_depth(write_then));
	pe_write = pet_expr_access_set_write(pe_write, 1);
	pe_write = pet_expr_access_set_read(pe_write, 0);
	pe = pet_expr_new_binary(type_size, pet_op_assign, pe_write, pe);
	return extract(stmt, pe);
}

/* Create a pet_scop with a single statement with name S_<stmt_nr>,
 * evaluating "cond" and writing the result to a virtual scalar,
 * as expressed by "index".
 */
struct pet_scop *PetScan::extract_non_affine_condition(Expr *cond, int stmt_nr,
	__isl_take isl_multi_pw_aff *index)
{
	pet_expr *expr, *write;
	struct pet_stmt *ps;
	SourceLocation loc = cond->getLocStart();
	int line = PP.getSourceManager().getExpansionLineNumber(loc);

	write = pet_expr_from_index(index);
	write = pet_expr_access_set_write(write, 1);
	write = pet_expr_access_set_read(write, 0);
	expr = extract_expr(cond);
	expr = resolve_nested(expr);
	expr = pet_expr_new_binary(1, pet_op_assign, write, expr);
	ps = pet_stmt_from_pet_expr(line, NULL, stmt_nr, expr);
	return pet_scop_from_pet_stmt(ctx, ps);
}

extern "C" {
	static __isl_give pet_expr *embed_access(__isl_take pet_expr *expr,
		void *user);
}

/* Precompose the access relation and the index expression associated
 * to "expr" with the function pointed to by "user",
 * thereby embedding the access relation in the domain of this function.
 * The initial domain of the access relation and the index expression
 * is the zero-dimensional domain.
 */
static __isl_give pet_expr *embed_access(__isl_take pet_expr *expr, void *user)
{
	isl_multi_aff *ma = (isl_multi_aff *) user;

	return pet_expr_access_pullback_multi_aff(expr, isl_multi_aff_copy(ma));
}

/* Precompose all access relations in "expr" with "ma", thereby
 * embedding them in the domain of "ma".
 */
static __isl_give pet_expr *embed(__isl_take pet_expr *expr,
	__isl_keep isl_multi_aff *ma)
{
	return pet_expr_map_access(expr, &embed_access, ma);
}

/* For each nested access parameter in the domain of "stmt",
 * construct a corresponding pet_expr, place it before the original
 * elements in stmt->args and record its position in "param2pos".
 * n is the number of nested access parameters.
 */
struct pet_stmt *PetScan::extract_nested(struct pet_stmt *stmt, int n,
	std::map<int,int> &param2pos)
{
	int i;
	isl_space *space;
	int n_arg;
	pet_expr **args;

	n_arg = stmt->n_arg;
	args = isl_calloc_array(ctx, pet_expr *, n + n_arg);
	if (!args)
		goto error;

	space = isl_set_get_space(stmt->domain);
	n_arg = extract_nested(space, 0, args, param2pos);
	isl_space_free(space);

	if (n_arg < 0)
		goto error;

	for (i = 0; i < stmt->n_arg; ++i)
		args[n_arg + i] = stmt->args[i];
	free(stmt->args);
	stmt->args = args;
	stmt->n_arg += n_arg;

	return stmt;
error:
	if (args) {
		for (i = 0; i < n; ++i)
			pet_expr_free(args[i]);
		free(args);
	}
	pet_stmt_free(stmt);
	return NULL;
}

/* Check whether any of the arguments i of "stmt" starting at position "n"
 * is equal to one of the first "n" arguments j.
 * If so, combine the constraints on arguments i and j and remove
 * argument i.
 */
static struct pet_stmt *remove_duplicate_arguments(struct pet_stmt *stmt, int n)
{
	int i, j;
	isl_map *map;

	if (!stmt)
		return NULL;
	if (n == 0)
		return stmt;
	if (n == stmt->n_arg)
		return stmt;

	map = isl_set_unwrap(stmt->domain);

	for (i = stmt->n_arg - 1; i >= n; --i) {
		for (j = 0; j < n; ++j)
			if (pet_expr_is_equal(stmt->args[i], stmt->args[j]))
				break;
		if (j >= n)
			continue;

		map = isl_map_equate(map, isl_dim_out, i, isl_dim_out, j);
		map = isl_map_project_out(map, isl_dim_out, i, 1);

		pet_expr_free(stmt->args[i]);
		for (j = i; j + 1 < stmt->n_arg; ++j)
			stmt->args[j] = stmt->args[j + 1];
		stmt->n_arg--;
	}

	stmt->domain = isl_map_wrap(map);
	if (!stmt->domain)
		goto error;
	return stmt;
error:
	pet_stmt_free(stmt);
	return NULL;
}

/* Look for parameters in the iteration domain of "stmt" that
 * refer to nested accesses.  In particular, these are
 * parameters with either no name or with name "__pet_expr".
 *
 * If there are any such parameters, then as many extra variables
 * (after identifying identical nested accesses) are inserted in the
 * range of the map wrapped inside the domain, before the original variables.
 * If the original domain is not a wrapped map, then a new wrapped
 * map is created with zero output dimensions.
 * The parameters are then equated to the corresponding output dimensions
 * and subsequently projected out, from the iteration domain,
 * the schedule and the access relations.
 * For each of the output dimensions, a corresponding argument
 * expression is inserted.  Initially they are created with
 * a zero-dimensional domain, so they have to be embedded
 * in the current iteration domain.
 * param2pos maps the position of the parameter to the position
 * of the corresponding output dimension in the wrapped map.
 */
struct pet_stmt *PetScan::resolve_nested(struct pet_stmt *stmt)
{
	int n;
	int nparam;
	unsigned n_arg;
	isl_map *map;
	isl_space *space;
	isl_multi_aff *ma;
	std::map<int,int> param2pos;

	if (!stmt)
		return NULL;

	n = pet_nested_n_in_set(stmt->domain);
	if (n == 0)
		return stmt;

	n_arg = stmt->n_arg;
	stmt = extract_nested(stmt, n, param2pos);
	if (!stmt)
		return NULL;

	n = stmt->n_arg - n_arg;
	nparam = isl_set_dim(stmt->domain, isl_dim_param);
	if (isl_set_is_wrapping(stmt->domain))
		map = isl_set_unwrap(stmt->domain);
	else
		map = isl_map_from_domain(stmt->domain);
	map = isl_map_insert_dims(map, isl_dim_out, 0, n);

	for (int i = nparam - 1; i >= 0; --i) {
		isl_id *id;

		if (!pet_nested_in_map(map, i))
			continue;

		id = pet_expr_access_get_id(stmt->args[param2pos[i]]);
		map = isl_map_set_dim_id(map, isl_dim_out, param2pos[i], id);
		map = isl_map_equate(map, isl_dim_param, i, isl_dim_out,
					param2pos[i]);
		map = isl_map_project_out(map, isl_dim_param, i, 1);
	}

	stmt->domain = isl_map_wrap(map);

	space = isl_space_unwrap(isl_set_get_space(stmt->domain));
	space = isl_space_from_domain(isl_space_domain(space));
	ma = isl_multi_aff_zero(space);
	for (int pos = 0; pos < n; ++pos)
		stmt->args[pos] = embed(stmt->args[pos], ma);
	isl_multi_aff_free(ma);

	stmt = pet_stmt_remove_nested_parameters(stmt);
	stmt = remove_duplicate_arguments(stmt, n);

	return stmt;
}

/* For each statement in "scop", move the parameters that correspond
 * to nested access into the ranges of the domains and create
 * corresponding argument expressions.
 */
struct pet_scop *PetScan::resolve_nested(struct pet_scop *scop)
{
	if (!scop)
		return NULL;

	for (int i = 0; i < scop->n_stmt; ++i) {
		scop->stmts[i] = resolve_nested(scop->stmts[i]);
		if (!scop->stmts[i])
			goto error;
	}

	return scop;
error:
	pet_scop_free(scop);
	return NULL;
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
bool PetScan::is_nested_allowed(__isl_keep isl_pw_aff *pa, pet_scop *scop)
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

		expr = extract_expr(id);
		allowed = pet_expr_get_type(expr) == pet_expr_access &&
			    !is_assigned(expr, scop);

		pet_expr_free(expr);
		isl_id_free(id);

		if (!allowed)
			return false;
	}

	return true;
}

/* Construct a pet_scop for a non-affine if statement.
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
struct pet_scop *PetScan::extract_non_affine_if(Expr *cond,
	struct pet_scop *scop_then, struct pet_scop *scop_else,
	bool have_else, int stmt_id)
{
	struct pet_scop *scop;
	isl_multi_pw_aff *test_index;
	int int_size;
	int save_n_stmt = n_stmt;

	test_index = pet_create_test_index(ctx, n_test++);
	n_stmt = stmt_id;
	scop = extract_non_affine_condition(cond, n_stmt++,
					isl_multi_pw_aff_copy(test_index));
	n_stmt = save_n_stmt;
	scop = scop_add_array(scop, test_index, ast_context);

	pet_skip_info skip;
	pet_skip_info_if_init(&skip, ctx, scop_then, scop_else, have_else, 0);
	int_size = ast_context.getTypeInfo(ast_context.IntTy).first / 8;
	pet_skip_info_if_extract_index(&skip, test_index, int_size,
					&n_stmt, &n_test);

	scop = pet_scop_prefix(scop, 0);
	scop_then = pet_scop_prefix(scop_then, 1);
	scop_then = pet_scop_filter(scop_then,
					isl_multi_pw_aff_copy(test_index), 1);
	if (have_else) {
		scop_else = pet_scop_prefix(scop_else, 1);
		scop_else = pet_scop_filter(scop_else, test_index, 0);
		scop_then = pet_scop_add_par(ctx, scop_then, scop_else);
	} else
		isl_multi_pw_aff_free(test_index);

	scop = pet_scop_add_seq(ctx, scop, scop_then);

	scop = pet_skip_info_if_add(&skip, scop, 2);

	return scop;
}

/* Construct a pet_scop for an if statement.
 *
 * If the condition fits the pattern of a conditional assignment,
 * then it is handled by extract_conditional_assignment.
 * Otherwise, we do the following.
 *
 * If the condition is affine, then the condition is added
 * to the iteration domains of the then branch, while the
 * opposite of the condition in added to the iteration domains
 * of the else branch, if any.
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
 *
 * If the condition is not affine, then the scop is created in
 * extract_non_affine_if.
 *
 * If there are any breaks or continues in the then and/or else
 * branches, then we may have to compute a new skip condition.
 * This is handled using a pet_skip_info object.
 * On initialization, the object checks if skip conditions need
 * to be computed.  If so, it does so in pet_skip_info_if_extract_cond and
 * adds them in pet_skip_info_if_add.
 */
struct pet_scop *PetScan::extract(IfStmt *stmt)
{
	struct pet_scop *scop_then, *scop_else = NULL, *scop;
	isl_pw_aff *cond;
	int stmt_id;
	int int_size;
	isl_set *set;
	isl_set *valid;

	clear_assignments clear(assigned_value);
	clear.TraverseStmt(stmt->getThen());
	if (stmt->getElse())
		clear.TraverseStmt(stmt->getElse());

	scop = extract_conditional_assignment(stmt);
	if (scop)
		return scop;

	cond = try_extract_nested_condition(stmt->getCond());
	if (allow_nested && (!cond || pet_nested_any_in_pw_aff(cond)))
		stmt_id = n_stmt++;

	{
		assigned_value_cache cache(assigned_value);
		scop_then = extract(stmt->getThen());
	}

	if (stmt->getElse()) {
		assigned_value_cache cache(assigned_value);
		scop_else = extract(stmt->getElse());
		if (options->autodetect) {
			if (scop_then && !scop_else) {
				partial = true;
				isl_pw_aff_free(cond);
				return scop_then;
			}
			if (!scop_then && scop_else) {
				partial = true;
				isl_pw_aff_free(cond);
				return scop_else;
			}
		}
	}

	if (cond &&
	    (!is_nested_allowed(cond, scop_then) ||
	     (stmt->getElse() && !is_nested_allowed(cond, scop_else)))) {
		isl_pw_aff_free(cond);
		cond = NULL;
	}
	if (allow_nested && !cond)
		return extract_non_affine_if(stmt->getCond(), scop_then,
					scop_else, stmt->getElse(), stmt_id);

	if (!cond)
		cond = extract_condition(stmt->getCond());

	pet_skip_info skip;
	pet_skip_info_if_init(&skip, ctx, scop_then, scop_else,
				stmt->getElse() != NULL, 1);
	pet_skip_info_if_extract_cond(&skip, cond, int_size, &n_stmt, &n_test);

	valid = isl_pw_aff_domain(isl_pw_aff_copy(cond));
	set = isl_pw_aff_non_zero_set(cond);
	scop = pet_scop_restrict(scop_then, isl_set_copy(set));

	if (stmt->getElse()) {
		set = isl_set_subtract(isl_set_copy(valid), set);
		scop_else = pet_scop_restrict(scop_else, set);
		scop = pet_scop_add_par(ctx, scop, scop_else);
	} else
		isl_set_free(set);
	scop = resolve_nested(scop);
	scop = pet_scop_restrict_context(scop, valid);

	if (pet_skip_info_has_skip(&skip))
		scop = pet_scop_prefix(scop, 0);
	scop = pet_skip_info_if_add(&skip, scop, 1);

	return scop;
}

/* Try and construct a pet_scop for a label statement.
 * We currently only allow labels on expression statements.
 */
struct pet_scop *PetScan::extract(LabelStmt *stmt)
{
	isl_id *label;
	Stmt *sub;

	sub = stmt->getSubStmt();
	if (!isa<Expr>(sub)) {
		unsupported(stmt);
		return NULL;
	}

	label = isl_id_alloc(ctx, stmt->getName(), NULL);

	return extract(sub, extract_expr(cast<Expr>(sub)), label);
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
struct pet_scop *PetScan::extract(ContinueStmt *stmt)
{
	pet_scop *scop;

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
struct pet_scop *PetScan::extract(BreakStmt *stmt)
{
	pet_scop *scop;
	isl_multi_pw_aff *skip;

	scop = pet_scop_empty(ctx);
	if (!scop)
		return NULL;

	skip = one_mpa(ctx);
	scop = pet_scop_set_skip(scop, pet_skip_now,
				    isl_multi_pw_aff_copy(skip));
	scop = pet_scop_set_skip(scop, pet_skip_later, skip);

	return scop;
}

/* Try and construct a pet_scop corresponding to "stmt".
 *
 * If "stmt" is a compound statement, then "skip_declarations"
 * indicates whether we should skip initial declarations in the
 * compound statement.
 *
 * If the constructed pet_scop is not a (possibly) partial representation
 * of "stmt", we update start and end of the pet_scop to those of "stmt".
 * In particular, if skip_declarations is set, then we may have skipped
 * declarations inside "stmt" and so the pet_scop may not represent
 * the entire "stmt".
 * Note that this function may be called with "stmt" referring to the entire
 * body of the function, including the outer braces.  In such cases,
 * skip_declarations will be set and the braces will not be taken into
 * account in scop->start and scop->end.
 */
struct pet_scop *PetScan::extract(Stmt *stmt, bool skip_declarations)
{
	struct pet_scop *scop;

	if (isa<Expr>(stmt))
		return extract(stmt, extract_expr(cast<Expr>(stmt)));

	switch (stmt->getStmtClass()) {
	case Stmt::WhileStmtClass:
		scop = extract(cast<WhileStmt>(stmt));
		break;
	case Stmt::ForStmtClass:
		scop = extract_for(cast<ForStmt>(stmt));
		break;
	case Stmt::IfStmtClass:
		scop = extract(cast<IfStmt>(stmt));
		break;
	case Stmt::CompoundStmtClass:
		scop = extract(cast<CompoundStmt>(stmt), skip_declarations);
		break;
	case Stmt::LabelStmtClass:
		scop = extract(cast<LabelStmt>(stmt));
		break;
	case Stmt::ContinueStmtClass:
		scop = extract(cast<ContinueStmt>(stmt));
		break;
	case Stmt::BreakStmtClass:
		scop = extract(cast<BreakStmt>(stmt));
		break;
	case Stmt::DeclStmtClass:
		scop = extract(cast<DeclStmt>(stmt));
		break;
	default:
		unsupported(stmt);
		return NULL;
	}

	if (partial || skip_declarations)
		return scop;

	scop = update_scop_start_end(scop, stmt->getSourceRange(), false);

	return scop;
}

/* Extract a clone of the kill statement in "scop".
 * "scop" is expected to have been created from a DeclStmt
 * and should have the kill as its first statement.
 */
struct pet_stmt *PetScan::extract_kill(struct pet_scop *scop)
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
	return pet_stmt_from_pet_expr(stmt->line, NULL, n_stmt++, kill);
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
 * a sequence of statements.
 *
 * "block" is set if the sequence respresents the children of
 * a compound statement.
 * "skip_declarations" is set if we should skip initial declarations
 * in the sequence of statements.
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
struct pet_scop *PetScan::extract(StmtRange stmt_range, bool block,
	bool skip_declarations)
{
	pet_scop *scop;
	StmtIterator i;
	int int_size;
	int j;
	bool partial_range = false;
	set<struct pet_stmt *> kills;
	set<struct pet_stmt *>::iterator it;

	int_size = ast_context.getTypeInfo(ast_context.IntTy).first / 8;

	scop = pet_scop_empty(ctx);
	for (i = stmt_range.first, j = 0; i != stmt_range.second; ++i, ++j) {
		Stmt *child = *i;
		struct pet_scop *scop_i;

		if (scop->n_stmt == 0 && skip_declarations &&
		    child->getStmtClass() == Stmt::DeclStmtClass)
			continue;

		scop_i = extract(child);
		if (scop->n_stmt != 0 && partial) {
			pet_scop_free(scop_i);
			break;
		}
		pet_skip_info skip;
		pet_skip_info_seq_init(&skip, ctx, scop, scop_i);
		pet_skip_info_seq_extract(&skip, int_size, &n_stmt, &n_test);
		if (pet_skip_info_has_skip(&skip))
			scop_i = pet_scop_prefix(scop_i, 0);
		if (scop_i && child->getStmtClass() == Stmt::DeclStmtClass) {
			if (block)
				kills.insert(extract_kill(scop_i));
			else
				scop_i = mark_exposed(scop_i);
		}
		scop_i = pet_scop_prefix(scop_i, j);
		if (options->autodetect) {
			if (scop_i)
				scop = pet_scop_add_seq(ctx, scop, scop_i);
			else
				partial_range = true;
			if (scop->n_stmt != 0 && !scop_i)
				partial = true;
		} else {
			scop = pet_scop_add_seq(ctx, scop, scop_i);
		}

		scop = pet_skip_info_seq_add(&skip, scop, j);

		if (partial || !scop)
			break;
	}

	for (it = kills.begin(); it != kills.end(); ++it) {
		pet_scop *scop_j;
		scop_j = pet_scop_from_pet_stmt(ctx, *it);
		scop_j = pet_scop_prefix(scop_j, j);
		scop = pet_scop_add_seq(ctx, scop, scop_j);
	}

	if (scop && partial_range) {
		if (scop->n_stmt == 0 || kills.size() != 0) {
			pet_scop_free(scop);
			return NULL;
		}
		partial = true;
	}

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
	if (start_off >= loc.start && end_off <= loc.end) {
		return extract(stmt);
	}

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

	return extract(StmtRange(start, end), false, false);
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

	valid = isl_pw_aff_nonneg_set(isl_pw_aff_copy(size));
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
		goto error;

	return array;
error:
	pet_array_free(array);
	return NULL;
}

/* Figure out the size of the array at position "pos" and all
 * subsequent positions from "type" and update "array" accordingly.
 */
struct pet_array *PetScan::set_upper_bounds(struct pet_array *array,
	const Type *type, int pos)
{
	const ArrayType *atype;
	isl_pw_aff *size;

	if (!array)
		return NULL;

	if (type->isPointerType()) {
		type = type->getPointeeType().getTypePtr();
		return set_upper_bounds(array, type, pos + 1);
	}
	if (!type->isArrayType())
		return array;

	type = type->getCanonicalTypeInternal().getTypePtr();
	atype = cast<ArrayType>(type);

	if (type->isConstantArrayType()) {
		const ConstantArrayType *ca = cast<ConstantArrayType>(atype);
		size = extract_affine(ca->getSize());
		array = update_size(array, pos, size);
	} else if (type->isVariableArrayType()) {
		const VariableArrayType *vla = cast<VariableArrayType>(atype);
		size = extract_affine(vla->getSizeExpr());
		array = update_size(array, pos, size);
	}

	type = atype->getElementType().getTypePtr();

	return set_upper_bounds(array, type, pos + 1);
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
 * based on the type of the variable.
 *
 * If the base type is that of a record with a top-level definition and
 * if "types" is not null, then the RecordDecl corresponding to the type
 * is added to "types".
 *
 * If the base type is that of a record with no top-level definition,
 * then we replace it by "<subfield>".
 */
struct pet_array *PetScan::extract_array(isl_ctx *ctx, ValueDecl *decl,
	lex_recorddecl_set *types)
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

	id = isl_id_alloc(ctx, decl->getName().str().c_str(), decl);
	dim = isl_space_set_alloc(ctx, 0, depth);
	dim = isl_space_set_tuple_id(dim, isl_dim_set, id);

	array->extent = isl_set_nat_universe(dim);

	dim = isl_space_params_alloc(ctx, 0);
	array->context = isl_set_universe(dim);

	array = set_upper_bounds(array, type, 0);
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
	vector<ValueDecl *> decls, lex_recorddecl_set *types)
{
	struct pet_array *array;
	vector<ValueDecl *>::iterator it;

	it = decls.begin();

	array = extract_array(ctx, *it, types);

	for (++it; it != decls.end(); ++it) {
		struct pet_array *parent;
		const char *base_name, *field_name;
		char *product_name;

		parent = array;
		array = extract_array(ctx, *it, types);
		if (!array)
			return pet_array_free(parent);

		base_name = isl_set_get_tuple_name(parent->extent);
		field_name = isl_set_get_tuple_name(array->extent);
		product_name = member_access_name(ctx, base_name, field_name);

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
 *
 * The context of "scop" is updated with the intersection of
 * the contexts of all arrays, i.e., constraints on the parameters
 * that ensure that the arrays have a valid (non-negative) size.
 *
 * If the any of the extracted arrays refers to a member access,
 * then also add the required types to "scop".
 */
struct pet_scop *PetScan::scan_arrays(struct pet_scop *scop)
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
		array = extract_array(ctx, *it, &types);
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

	if (options->autodetect)
		scop = extract(stmt, true);
	else {
		scop = scan(stmt);
		scop = pet_scop_update_start_end(scop, loc.start, loc.end);
	}
	scop = pet_scop_detect_parameter_accesses(scop);
	scop = scan_arrays(scop);
	scop = add_parameter_bounds(scop);
	scop = pet_scop_gist(scop, value_bounds);

	return scop;
}
