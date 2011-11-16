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
#include <map>
#include <iostream>
#include <clang/AST/ASTDiagnostic.h>
#include <clang/AST/Expr.h>
#include <clang/AST/RecursiveASTVisitor.h>

#include <isl/id.h>
#include <isl/space.h>
#include <isl/aff.h>
#include <isl/set.h>

#include "scan.h"
#include "scop.h"
#include "scop_plus.h"

#include "config.h"

using namespace std;
using namespace clang;


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
	map<ValueDecl *, Expr *> &assigned_value;
	set<UnaryOperator *> skip;

	clear_assignments(map<ValueDecl *, Expr *> &assigned_value) :
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

		if (expr->getOpcode() != UO_AddrOf)
			return true;
		if (skip.find(expr) != skip.end())
			return true;

		arg = expr->getSubExpr();
		if (arg->getStmtClass() != Stmt::DeclRefExprClass)
			return true;
		ref = cast<DeclRefExpr>(arg);
		decl = ref->getDecl();
		assigned_value[decl] = NULL;
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
		assigned_value[decl] = NULL;
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
	map<ValueDecl *, Expr *> &assigned_value;
	map<ValueDecl *, Expr *> cache;

	assigned_value_cache(map<ValueDecl *, Expr *> &assigned_value) :
		assigned_value(assigned_value), cache(assigned_value) {}
	~assigned_value_cache() {
		map<ValueDecl *, Expr *>::iterator it = cache.begin();
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

/* Called if we found something we (currently) cannot handle.
 * We'll provide more informative warnings later.
 *
 * We only actually complain if autodetect is false.
 */
void PetScan::unsupported(Stmt *stmt)
{
	if (autodetect)
		return;

	SourceLocation loc = stmt->getLocStart();
	DiagnosticsEngine &diag = PP.getDiagnostics();
	unsigned id = diag.getCustomDiagID(DiagnosticsEngine::Warning,
					   "unsupported");
	DiagnosticBuilder B = diag.Report(loc, id) << stmt->getSourceRange();
}

/* Extract an integer from "expr" and store it in "v".
 */
int PetScan::extract_int(IntegerLiteral *expr, isl_int *v)
{
	const Type *type = expr->getType().getTypePtr();
	int is_signed = type->hasSignedIntegerRepresentation();

	if (is_signed) {
		int64_t i = expr->getValue().getSExtValue();
		isl_int_set_si(*v, i);
	} else {
		uint64_t i = expr->getValue().getZExtValue();
		isl_int_set_ui(*v, i);
	}

	return 0;
}

/* Extract an affine expression from the IntegerLiteral "expr".
 */
__isl_give isl_pw_aff *PetScan::extract_affine(IntegerLiteral *expr)
{
	isl_space *dim = isl_space_params_alloc(ctx, 0);
	isl_local_space *ls = isl_local_space_from_space(isl_space_copy(dim));
	isl_aff *aff = isl_aff_zero_on_domain(ls);
	isl_set *dom = isl_set_universe(dim);
	isl_int v;

	isl_int_init(v);
	extract_int(expr, &v);
	aff = isl_aff_add_constant(aff, v);
	isl_int_clear(v);

	return isl_pw_aff_alloc(dom, aff);
}

/* Extract an affine expression from the APInt "val".
 */
__isl_give isl_pw_aff *PetScan::extract_affine(const llvm::APInt &val)
{
	isl_space *dim = isl_space_params_alloc(ctx, 0);
	isl_local_space *ls = isl_local_space_from_space(isl_space_copy(dim));
	isl_aff *aff = isl_aff_zero_on_domain(ls);
	isl_set *dom = isl_set_universe(dim);
	isl_int v;

	isl_int_init(v);
	isl_int_set_ui(v, val.getZExtValue());
	aff = isl_aff_add_constant(aff, v);
	isl_int_clear(v);

	return isl_pw_aff_alloc(dom, aff);
}

__isl_give isl_pw_aff *PetScan::extract_affine(ImplicitCastExpr *expr)
{
	return extract_affine(expr->getSubExpr());
}

/* Extract an affine expression from the DeclRefExpr "expr".
 *
 * If the variable has been assigned a value, then we check whether
 * we know what expression was assigned and whether this expression
 * is affine.  If so, we convert the expression to an isl_pw_aff
 * and to an extra parameter otherwise (provided nesting_enabled is set).
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
		if (assigned_value[decl] && is_affine(assigned_value[decl]))
			return extract_affine(assigned_value[decl]);
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
	Expr *rhs_expr;
	isl_pw_aff *lhs, *lhs_f, *lhs_c;
	isl_pw_aff *res;
	isl_int v;
	isl_set *cond;

	rhs_expr = expr->getRHS();
	if (rhs_expr->getStmtClass() != Stmt::IntegerLiteralClass) {
		unsupported(expr);
		return NULL;
	}

	lhs = extract_affine(expr->getLHS());
	cond = isl_pw_aff_nonneg_set(isl_pw_aff_copy(lhs));

	isl_int_init(v);
	extract_int(cast<IntegerLiteral>(rhs_expr), &v);
	lhs = isl_pw_aff_scale_down(lhs, v);
	isl_int_clear(v);

	lhs_f = isl_pw_aff_floor(isl_pw_aff_copy(lhs));
	lhs_c = isl_pw_aff_ceil(lhs);
	res = isl_pw_aff_cond(cond, lhs_f, lhs_c);

	return res;
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
	Expr *rhs_expr;
	isl_pw_aff *lhs, *lhs_f, *lhs_c;
	isl_pw_aff *res;
	isl_int v;
	isl_set *cond;

	rhs_expr = expr->getRHS();
	if (rhs_expr->getStmtClass() != Stmt::IntegerLiteralClass) {
		unsupported(expr);
		return NULL;
	}

	lhs = extract_affine(expr->getLHS());
	cond = isl_pw_aff_nonneg_set(isl_pw_aff_copy(lhs));

	isl_int_init(v);
	extract_int(cast<IntegerLiteral>(rhs_expr), &v);
	res = isl_pw_aff_scale_down(isl_pw_aff_copy(lhs), v);

	lhs_f = isl_pw_aff_floor(isl_pw_aff_copy(res));
	lhs_c = isl_pw_aff_ceil(res);
	res = isl_pw_aff_cond(cond, lhs_f, lhs_c);

	res = isl_pw_aff_scale(res, v);
	isl_int_clear(v);

	res = isl_pw_aff_sub(lhs, res);

	return res;
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
	isl_int mod;

	isl_int_init(mod);
	isl_int_set_si(mod, 1);
	isl_int_mul_2exp(mod, mod, width);

	pwaff = isl_pw_aff_mod(pwaff, mod);

	isl_int_clear(mod);

	return pwaff;
}

/* Extract an affine expression from some binary operations.
 * If the result of the expression is unsigned, then we wrap it
 * based on the size of the type.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(BinaryOperator *expr)
{
	isl_pw_aff *res;

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
	default:
		unsupported(expr);
		return NULL;
	}

	if (expr->getType()->isUnsignedIntegerType())
		res = wrap(res, ast_context.getIntWidth(expr->getType()));

	return res;
}

/* Extract an affine expression from a negation operation.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(UnaryOperator *expr)
{
	if (expr->getOpcode() == UO_Minus)
		return isl_pw_aff_neg(extract_affine(expr->getSubExpr()));

	unsupported(expr);
	return NULL;
}

__isl_give isl_pw_aff *PetScan::extract_affine(ParenExpr *expr)
{
	return extract_affine(expr->getSubExpr());
}

/* Extract an affine expression from some special function calls.
 * In particular, we handle "min", "max", "ceild" and "floord".
 * In case of the latter two, the second argument needs to be
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
	} else if (name == "floord" || name == "ceild") {
		isl_int v;
		Expr *arg2 = expr->getArg(1);

		if (arg2->getStmtClass() != Stmt::IntegerLiteralClass) {
			unsupported(expr);
			return NULL;
		}
		aff1 = extract_affine(expr->getArg(0));
		isl_int_init(v);
		extract_int(cast<IntegerLiteral>(arg2), &v);
		aff1 = isl_pw_aff_scale_down(aff1, v);
		isl_int_clear(v);
		if (name == "floord")
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
 * The new parameter is resolved in resolve_nested.
 */
isl_pw_aff *PetScan::nested_access(Expr *expr)
{
	isl_id *id;
	isl_space *dim;
	isl_aff *aff;
	isl_set *dom;

	if (!nesting_enabled) {
		unsupported(expr);
		return NULL;
	}

	id = isl_id_alloc(ctx, NULL, expr);
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

/* Extract an affine expression from a conditional operation.
 */
__isl_give isl_pw_aff *PetScan::extract_affine(ConditionalOperator *expr)
{
	isl_set *cond;
	isl_pw_aff *lhs, *rhs;

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
	case Stmt::ConditionalOperatorClass:
		return extract_affine(cast<ConditionalOperator>(expr));
	default:
		unsupported(expr);
	}
	return NULL;
}

__isl_give isl_map *PetScan::extract_access(ImplicitCastExpr *expr)
{
	return extract_access(expr->getSubExpr());
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

/* Return the element type of the given array type.
 */
static QualType base_type(QualType qt)
{
	const Type *type = qt.getTypePtr();

	if (type->isPointerType())
		return base_type(type->getPointeeType());
	if (type->isArrayType()) {
		const ArrayType *atype;
		type = type->getCanonicalTypeInternal().getTypePtr();
		atype = cast<ArrayType>(type);
		return base_type(atype->getElementType());
	}
	return qt;
}

/* Extract an access relation from a reference to a variable.
 * If the variable has name "A" and its type corresponds to an
 * array of depth d, then the returned access relation is of the
 * form
 *
 *	{ [] -> A[i_1,...,i_d] }
 */
__isl_give isl_map *PetScan::extract_access(DeclRefExpr *expr)
{
	ValueDecl *decl = expr->getDecl();
	int depth = array_depth(decl->getType().getTypePtr());
	isl_id *id = isl_id_alloc(ctx, decl->getName().str().c_str(), decl);
	isl_space *dim = isl_space_alloc(ctx, 0, 0, depth);
	isl_map *access_rel;

	dim = isl_space_set_tuple_id(dim, isl_dim_out, id);

	access_rel = isl_map_universe(dim);

	return access_rel;
}

/* Extract an access relation from an integer contant.
 * If the value of the constant is "v", then the returned access relation
 * is
 *
 *	{ [] -> [v] }
 */
__isl_give isl_map *PetScan::extract_access(IntegerLiteral *expr)
{
	return isl_map_from_range(isl_set_from_pw_aff(extract_affine(expr)));
}

/* Try and extract an access relation from the given Expr.
 * Return NULL if it doesn't work out.
 */
__isl_give isl_map *PetScan::extract_access(Expr *expr)
{
	switch (expr->getStmtClass()) {
	case Stmt::ImplicitCastExprClass:
		return extract_access(cast<ImplicitCastExpr>(expr));
	case Stmt::DeclRefExprClass:
		return extract_access(cast<DeclRefExpr>(expr));
	case Stmt::ArraySubscriptExprClass:
		return extract_access(cast<ArraySubscriptExpr>(expr));
	default:
		unsupported(expr);
	}
	return NULL;
}

/* Assign the affine expression "index" to the output dimension "pos" of "map"
 * and return the result.
 */
__isl_give isl_map *set_index(__isl_take isl_map *map, int pos,
	__isl_take isl_pw_aff *index)
{
	isl_map *index_map;
	int len = isl_map_dim(map, isl_dim_out);
	isl_id *id;

	index_map = isl_map_from_range(isl_set_from_pw_aff(index));
	index_map = isl_map_insert_dims(index_map, isl_dim_out, 0, pos);
	index_map = isl_map_add_dims(index_map, isl_dim_out, len - pos - 1);
	id = isl_map_get_tuple_id(map, isl_dim_out);
	index_map = isl_map_set_tuple_id(index_map, isl_dim_out, id);

	map = isl_map_intersect(map, index_map);

	return map;
}

/* Extract an access relation from the given array subscript expression.
 * If nesting is allowed in general, then we turn it on while
 * examining the index expression.
 *
 * We first extract an access relation from the base.
 * This will result in an access relation with a range that corresponds
 * to the array being accessed and with earlier indices filled in already.
 * We then extract the current index and fill that in as well.
 * The position of the current index is based on the type of base.
 * If base is the actual array variable, then the depth of this type
 * will be the same as the depth of the array and we will fill in
 * the first array index.
 * Otherwise, the depth of the base type will be smaller and we will fill
 * in a later index.
 */
__isl_give isl_map *PetScan::extract_access(ArraySubscriptExpr *expr)
{
	Expr *base = expr->getBase();
	Expr *idx = expr->getIdx();
	isl_pw_aff *index;
	isl_map *base_access;
	isl_map *access;
	int depth = array_depth(base->getType().getTypePtr());
	int pos;
	bool save_nesting = nesting_enabled;

	nesting_enabled = allow_nested;

	base_access = extract_access(base);
	index = extract_affine(idx);

	nesting_enabled = save_nesting;

	pos = isl_map_dim(base_access, isl_dim_out) - depth;
	access = set_index(base_access, pos, index);

	return access;
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

/* Extract a set of values satisfying the comparison "LHS op RHS"
 * "comp" is the original statement that "LHS op RHS" is derived from
 * and is used for diagnostics.
 *
 * If the comparison is of the form
 *
 *	a <= min(b,c)
 *
 * then the set is constructed as the intersection of the set corresponding
 * to the comparisons
 *
 *	a <= b		and		a <= c
 *
 * A similar optimization is performed for max(a,b) <= c.
 * We do this because that will lead to simpler representations of the set.
 * If isl is ever enhanced to explicitly deal with min and max expressions,
 * this optimization can be removed.
 */
__isl_give isl_set *PetScan::extract_comparison(BinaryOperatorKind op,
	Expr *LHS, Expr *RHS, Stmt *comp)
{
	isl_pw_aff *lhs;
	isl_pw_aff *rhs;
	isl_set *cond;

	if (op == BO_GT)
		return extract_comparison(BO_LT, RHS, LHS, comp);
	if (op == BO_GE)
		return extract_comparison(BO_LE, RHS, LHS, comp);

	if (op == BO_LT || op == BO_LE) {
		Expr *expr1, *expr2;
		isl_set *set1, *set2;
		if (is_min(RHS, expr1, expr2)) {
			set1 = extract_comparison(op, LHS, expr1, comp);
			set2 = extract_comparison(op, LHS, expr2, comp);
			return isl_set_intersect(set1, set2);
		}
		if (is_max(LHS, expr1, expr2)) {
			set1 = extract_comparison(op, expr1, RHS, comp);
			set2 = extract_comparison(op, expr2, RHS, comp);
			return isl_set_intersect(set1, set2);
		}
	}

	lhs = extract_affine(LHS);
	rhs = extract_affine(RHS);

	switch (op) {
	case BO_LT:
		cond = isl_pw_aff_lt_set(lhs, rhs);
		break;
	case BO_LE:
		cond = isl_pw_aff_le_set(lhs, rhs);
		break;
	case BO_EQ:
		cond = isl_pw_aff_eq_set(lhs, rhs);
		break;
	case BO_NE:
		cond = isl_pw_aff_ne_set(lhs, rhs);
		break;
	default:
		isl_pw_aff_free(lhs);
		isl_pw_aff_free(rhs);
		unsupported(comp);
		return NULL;
	}

	cond = isl_set_coalesce(cond);

	return cond;
}

__isl_give isl_set *PetScan::extract_comparison(BinaryOperator *comp)
{
	return extract_comparison(comp->getOpcode(), comp->getLHS(),
				comp->getRHS(), comp);
}

/* Extract a set of values satisfying the negation (logical not)
 * of a subexpression.
 */
__isl_give isl_set *PetScan::extract_boolean(UnaryOperator *op)
{
	isl_set *cond;

	cond = extract_condition(op->getSubExpr());

	return isl_set_complement(cond);
}

/* Extract a set of values satisfying the union (logical or)
 * or intersection (logical and) of two subexpressions.
 */
__isl_give isl_set *PetScan::extract_boolean(BinaryOperator *comp)
{
	isl_set *lhs;
	isl_set *rhs;
	isl_set *cond;

	lhs = extract_condition(comp->getLHS());
	rhs = extract_condition(comp->getRHS());

	switch (comp->getOpcode()) {
	case BO_LAnd:
		cond = isl_set_intersect(lhs, rhs);
		break;
	case BO_LOr:
		cond = isl_set_union(lhs, rhs);
		break;
	default:
		isl_set_free(lhs);
		isl_set_free(rhs);
		unsupported(comp);
		return NULL;
	}

	return cond;
}

__isl_give isl_set *PetScan::extract_condition(UnaryOperator *expr)
{
	switch (expr->getOpcode()) {
	case UO_LNot:
		return extract_boolean(expr);
	default:
		unsupported(expr);
		return NULL;
	}
}

/* Extract a set of values satisfying the condition "expr != 0".
 */
__isl_give isl_set *PetScan::extract_implicit_condition(Expr *expr)
{
	return isl_pw_aff_non_zero_set(extract_affine(expr));
}

/* Extract a set of values satisfying the condition expressed by "expr".
 *
 * If the expression doesn't look like a condition, we assume it
 * is an affine expression and return the condition "expr != 0".
 */
__isl_give isl_set *PetScan::extract_condition(Expr *expr)
{
	BinaryOperator *comp;

	if (!expr)
		return isl_set_universe(isl_space_params_alloc(ctx, 0));

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

static enum pet_op_type UnaryOperatorKind2pet_op_type(UnaryOperatorKind kind)
{
	switch (kind) {
	case UO_Minus:
		return pet_op_minus;
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
	case BO_EQ:
		return pet_op_eq;
	case BO_LE:
		return pet_op_le;
	case BO_LT:
		return pet_op_lt;
	case BO_GT:
		return pet_op_gt;
	default:
		return pet_op_last;
	}
}

/* Construct a pet_expr representing a unary operator expression.
 */
struct pet_expr *PetScan::extract_expr(UnaryOperator *expr)
{
	struct pet_expr *arg;
	enum pet_op_type op;

	op = UnaryOperatorKind2pet_op_type(expr->getOpcode());
	if (op == pet_op_last) {
		unsupported(expr);
		return NULL;
	}

	arg = extract_expr(expr->getSubExpr());

	return pet_expr_new_unary(ctx, op, arg);
}

/* Mark the given access pet_expr as a write.
 * If a scalar is being accessed, then mark its value
 * as unknown in assigned_value.
 */
void PetScan::mark_write(struct pet_expr *access)
{
	isl_id *id;
	ValueDecl *decl;

	access->acc.write = 1;
	access->acc.read = 0;

	if (isl_map_dim(access->acc.access, isl_dim_out) != 0)
		return;

	id = isl_map_get_tuple_id(access->acc.access, isl_dim_out);
	decl = (ValueDecl *) isl_id_get_user(id);
	assigned_value[decl] = NULL;
	isl_id_free(id);
}

/* Construct a pet_expr representing a binary operator expression.
 *
 * If the top level operator is an assignment and the LHS is an access,
 * then we mark that access as a write.  If the operator is a compound
 * assignment, the access is marked as both a read and a write.
 *
 * If "expr" assigns something to a scalar variable, then we keep track
 * of the assigned expression in assigned_value so that we can plug
 * it in when we later come across the same variable.
 */
struct pet_expr *PetScan::extract_expr(BinaryOperator *expr)
{
	struct pet_expr *lhs, *rhs;
	enum pet_op_type op;

	op = BinaryOperatorKind2pet_op_type(expr->getOpcode());
	if (op == pet_op_last) {
		unsupported(expr);
		return NULL;
	}

	lhs = extract_expr(expr->getLHS());
	rhs = extract_expr(expr->getRHS());

	if (expr->isAssignmentOp() && lhs && lhs->type == pet_expr_access) {
		mark_write(lhs);
		if (expr->isCompoundAssignmentOp())
			lhs->acc.read = 1;
	}

	if (expr->getOpcode() == BO_Assign &&
	    lhs && lhs->type == pet_expr_access &&
	    isl_map_dim(lhs->acc.access, isl_dim_out) == 0) {
		isl_id *id = isl_map_get_tuple_id(lhs->acc.access, isl_dim_out);
		ValueDecl *decl = (ValueDecl *) isl_id_get_user(id);
		assigned_value[decl] = expr->getRHS();
		isl_id_free(id);
	}

	return pet_expr_new_binary(ctx, op, lhs, rhs);
}

/* Construct a pet_expr representing a conditional operation.
 */
struct pet_expr *PetScan::extract_expr(ConditionalOperator *expr)
{
	struct pet_expr *cond, *lhs, *rhs;

	cond = extract_expr(expr->getCond());
	lhs = extract_expr(expr->getTrueExpr());
	rhs = extract_expr(expr->getFalseExpr());

	return pet_expr_new_ternary(ctx, cond, lhs, rhs);
}

struct pet_expr *PetScan::extract_expr(ImplicitCastExpr *expr)
{
	return extract_expr(expr->getSubExpr());
}

/* Construct a pet_expr representing a floating point value.
 */
struct pet_expr *PetScan::extract_expr(FloatingLiteral *expr)
{
	return pet_expr_new_double(ctx, expr->getValueAsApproximateDouble());
}

/* Extract an access relation from "expr" and then convert it into
 * a pet_expr.
 */
struct pet_expr *PetScan::extract_access_expr(Expr *expr)
{
	isl_map *access;
	struct pet_expr *pe;

	switch (expr->getStmtClass()) {
	case Stmt::ArraySubscriptExprClass:
		access = extract_access(cast<ArraySubscriptExpr>(expr));
		break;
	case Stmt::DeclRefExprClass:
		access = extract_access(cast<DeclRefExpr>(expr));
		break;
	case Stmt::IntegerLiteralClass:
		access = extract_access(cast<IntegerLiteral>(expr));
		break;
	default:
		unsupported(expr);
		return NULL;
	}

	pe = pet_expr_from_access(access);

	return pe;
}

struct pet_expr *PetScan::extract_expr(ParenExpr *expr)
{
	return extract_expr(expr->getSubExpr());
}

/* Construct a pet_expr representing a function call.
 *
 * If we are passing along a pointer to an array element
 * or an entire row or even higher dimensional slice of an array,
 * then the function being called may write into the array.
 *
 * We assume here that if the function is declared to take a pointer
 * to a const type, then the function will perform a read
 * and that otherwise, it will perform a write.
 */
struct pet_expr *PetScan::extract_expr(CallExpr *expr)
{
	struct pet_expr *res = NULL;
	FunctionDecl *fd;
	string name;

	fd = expr->getDirectCallee();
	if (!fd) {
		unsupported(expr);
		return NULL;
	}

	name = fd->getDeclName().getAsString();
	res = pet_expr_new_call(ctx, name.c_str(), expr->getNumArgs());
	if (!res)
		return NULL;

	for (int i = 0; i < expr->getNumArgs(); ++i) {
		Expr *arg = expr->getArg(i);
		int is_addr = 0;

		if (arg->getStmtClass() == Stmt::ImplicitCastExprClass) {
			ImplicitCastExpr *ice = cast<ImplicitCastExpr>(arg);
			arg = ice->getSubExpr();
		}
		if (arg->getStmtClass() == Stmt::UnaryOperatorClass) {
			UnaryOperator *op = cast<UnaryOperator>(arg);
			if (op->getOpcode() == UO_AddrOf) {
				is_addr = 1;
				arg = op->getSubExpr();
			}
		}
		res->args[i] = PetScan::extract_expr(arg);
		if (!res->args[i])
			goto error;
		if (arg->getStmtClass() == Stmt::ArraySubscriptExprClass &&
		    array_depth(arg->getType().getTypePtr()) > 0)
			is_addr = 1;
		if (is_addr && res->args[i]->type == pet_expr_access) {
			ParmVarDecl *parm = fd->getParamDecl(i);
			if (!const_base(parm->getType()))
				mark_write(res->args[i]);
		}
	}

	return res;
error:
	pet_expr_free(res);
	return NULL;
}

/* Try and onstruct a pet_expr representing "expr".
 */
struct pet_expr *PetScan::extract_expr(Expr *expr)
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
	case Stmt::IntegerLiteralClass:
		return extract_access_expr(expr);
	case Stmt::FloatingLiteralClass:
		return extract_expr(cast<FloatingLiteral>(expr));
	case Stmt::ParenExprClass:
		return extract_expr(cast<ParenExpr>(expr));
	case Stmt::ConditionalOperatorClass:
		return extract_expr(cast<ConditionalOperator>(expr));
	case Stmt::CallExprClass:
		return extract_expr(cast<CallExpr>(expr));
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
 * "inc" is accordingly set to 1 or -1.
 */
bool PetScan::check_unary_increment(UnaryOperator *op, clang::ValueDecl *iv,
	isl_int &inc)
{
	Expr *sub;
	DeclRefExpr *ref;

	if (!op->isIncrementDecrementOp()) {
		unsupported(op);
		return false;
	}

	if (op->isIncrementOp())
		isl_int_set_si(inc, 1);
	else
		isl_int_set_si(inc, -1);

	sub = op->getSubExpr();
	if (sub->getStmtClass() != Stmt::DeclRefExprClass) {
		unsupported(op);
		return false;
	}

	ref = cast<DeclRefExpr>(sub);
	if (ref->getDecl() != iv) {
		unsupported(op);
		return false;
	}

	return true;
}

/* If the isl_pw_aff on which isl_pw_aff_foreach_piece is called
 * has a single constant expression on a universe domain, then
 * put this constant in *user.
 */
static int extract_cst(__isl_take isl_set *set, __isl_take isl_aff *aff,
	void *user)
{
	isl_int *inc = (isl_int *)user;
	int res = 0;

	if (!isl_set_plain_is_universe(set) || !isl_aff_is_cst(aff))
		res = -1;
	else
		isl_aff_get_constant(aff, inc);

	isl_set_free(set);
	isl_aff_free(aff);

	return res;
}

/* Check if op is of the form
 *
 *	iv = iv + inc
 *
 * with inc a constant and set "inc" accordingly.
 *
 * We extract an affine expression from the RHS and the subtract iv.
 * The result should be a constant.
 */
bool PetScan::check_binary_increment(BinaryOperator *op, clang::ValueDecl *iv,
	isl_int &inc)
{
	Expr *lhs;
	DeclRefExpr *ref;
	isl_id *id;
	isl_space *dim;
	isl_aff *aff;
	isl_pw_aff *val;

	if (op->getOpcode() != BO_Assign) {
		unsupported(op);
		return false;
	}

	lhs = op->getLHS();
	if (lhs->getStmtClass() != Stmt::DeclRefExprClass) {
		unsupported(op);
		return false;
	}

	ref = cast<DeclRefExpr>(lhs);
	if (ref->getDecl() != iv) {
		unsupported(op);
		return false;
	}

	val = extract_affine(op->getRHS());

	id = isl_id_alloc(ctx, iv->getName().str().c_str(), iv);

	dim = isl_space_params_alloc(ctx, 1);
	dim = isl_space_set_dim_id(dim, isl_dim_param, 0, id);
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient_si(aff, isl_dim_param, 0, 1);

	val = isl_pw_aff_sub(val, isl_pw_aff_from_aff(aff));

	if (isl_pw_aff_foreach_piece(val, &extract_cst, &inc) < 0) {
		isl_pw_aff_free(val);
		unsupported(op);
		return false;
	}

	isl_pw_aff_free(val);

	return true;
}

/* Check that op is of the form iv += cst or iv -= cst.
 * "inc" is set to cst or -cst accordingly.
 */
bool PetScan::check_compound_increment(CompoundAssignOperator *op,
	clang::ValueDecl *iv, isl_int &inc)
{
	Expr *lhs, *rhs;
	DeclRefExpr *ref;
	bool neg = false;

	BinaryOperatorKind opcode;

	opcode = op->getOpcode();
	if (opcode != BO_AddAssign && opcode != BO_SubAssign) {
		unsupported(op);
		return false;
	}
	if (opcode == BO_SubAssign)
		neg = true;

	lhs = op->getLHS();
	if (lhs->getStmtClass() != Stmt::DeclRefExprClass) {
		unsupported(op);
		return false;
	}

	ref = cast<DeclRefExpr>(lhs);
	if (ref->getDecl() != iv) {
		unsupported(op);
		return false;
	}

	rhs = op->getRHS();

	if (rhs->getStmtClass() == Stmt::UnaryOperatorClass) {
		UnaryOperator *op = cast<UnaryOperator>(rhs);
		if (op->getOpcode() != UO_Minus) {
			unsupported(op);
			return false;
		}

		neg = !neg;

		rhs = op->getSubExpr();
	}

	if (rhs->getStmtClass() != Stmt::IntegerLiteralClass) {
		unsupported(op);
		return false;
	}

	extract_int(cast<IntegerLiteral>(rhs), &inc);
	if (neg)
		isl_int_neg(inc, inc);

	return true;
}

/* Check that the increment of the given for loop increments
 * (or decrements) the induction variable "iv".
 * "up" is set to true if the induction variable is incremented.
 */
bool PetScan::check_increment(ForStmt *stmt, ValueDecl *iv, isl_int &v)
{
	Stmt *inc = stmt->getInc();

	if (!inc) {
		unsupported(stmt);
		return false;
	}

	if (inc->getStmtClass() == Stmt::UnaryOperatorClass)
		return check_unary_increment(cast<UnaryOperator>(inc), iv, v);
	if (inc->getStmtClass() == Stmt::CompoundAssignOperatorClass)
		return check_compound_increment(
				cast<CompoundAssignOperator>(inc), iv, v);
	if (inc->getStmtClass() == Stmt::BinaryOperatorClass)
		return check_binary_increment(cast<BinaryOperator>(inc), iv, v);

	unsupported(inc);
	return false;
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
 */
struct pet_scop *PetScan::extract_infinite_loop(Stmt *body)
{
	isl_id *id;
	isl_space *dim;
	isl_set *domain;
	isl_map *sched;
	struct pet_scop *scop;

	scop = extract(body);
	if (!scop)
		return NULL;

	id = isl_id_alloc(ctx, "t", NULL);
	domain = isl_set_nat_universe(isl_space_set_alloc(ctx, 0, 1));
	domain = isl_set_set_dim_id(domain, isl_dim_set, 0, isl_id_copy(id));
	dim = isl_space_from_domain(isl_set_get_space(domain));
	dim = isl_space_add_dims(dim, isl_dim_out, 1);
	sched = isl_map_universe(dim);
	sched = isl_map_equate(sched, isl_dim_in, 0, isl_dim_out, 0);
	scop = pet_scop_embed(scop, domain, sched, id);

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
	return extract_infinite_loop(stmt->getBody());
}

/* Check if the while loop is of the form
 *
 *	while (1)
 *		body
 *
 * If so, construct a scop for an infinite loop around body.
 * Otherwise, fail.
 */
struct pet_scop *PetScan::extract(WhileStmt *stmt)
{
	Expr *cond;
	isl_set *set;
	int is_universe;

	cond = stmt->getCond();
	if (!cond) {
		unsupported(stmt);
		return NULL;
	}

	set = extract_condition(cond);
	is_universe = isl_set_plain_is_universe(set);
	isl_set_free(set);

	if (!is_universe) {
		unsupported(stmt);
		return NULL;
	}

	return extract_infinite_loop(stmt->getBody());
}

/* Check whether "cond" expresses a simple loop bound
 * on the only set dimension.
 * In particular, if "up" is set then "cond" should contain only
 * upper bounds on the set dimension.
 * Otherwise, it should contain only lower bounds.
 */
static bool is_simple_bound(__isl_keep isl_set *cond, isl_int inc)
{
	if (isl_int_is_pos(inc))
		return !isl_set_dim_has_lower_bound(cond, isl_dim_set, 0);
	else
		return !isl_set_dim_has_upper_bound(cond, isl_dim_set, 0);
}

/* Extend a condition on a given iteration of a loop to one that
 * imposes the same condition on all previous iterations.
 * "domain" expresses the lower [upper] bound on the iterations
 * when up is set [not set].
 *
 * In particular, we construct the condition (when up is set)
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
	__isl_take isl_set *domain, isl_int inc)
{
	isl_map *previous_to_this;

	if (isl_int_is_pos(inc))
		previous_to_this = isl_map_lex_le(isl_set_get_space(domain));
	else
		previous_to_this = isl_map_lex_ge(isl_set_get_space(domain));

	previous_to_this = isl_map_intersect_domain(previous_to_this, domain);

	cond = isl_set_complement(cond);
	cond = isl_set_apply(cond, previous_to_this);
	cond = isl_set_complement(cond);

	return cond;
}

/* Construct a domain of the form
 *
 * [id] -> { [] : exists a: id = init + a * inc and a >= 0 }
 */
static __isl_give isl_set *strided_domain(__isl_take isl_id *id,
	__isl_take isl_pw_aff *init, isl_int inc)
{
	isl_aff *aff;
	isl_space *dim;
	isl_set *set;

	init = isl_pw_aff_insert_dims(init, isl_dim_in, 0, 1);
	dim = isl_pw_aff_get_domain_space(init);
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient(aff, isl_dim_in, 0, inc);
	init = isl_pw_aff_add(init, isl_pw_aff_from_aff(aff));

	dim = isl_space_set_alloc(isl_pw_aff_get_ctx(init), 1, 1);
	dim = isl_space_set_dim_id(dim, isl_dim_param, 0, id);
	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient_si(aff, isl_dim_param, 0, 1);

	set = isl_pw_aff_eq_set(isl_pw_aff_from_aff(aff), init);

	set = isl_set_lower_bound_si(set, isl_dim_set, 0, 0);

	return isl_set_project_out(set, isl_dim_set, 0, 1);
}

static unsigned get_type_size(ValueDecl *decl)
{
	return decl->getASTContext().getIntWidth(decl->getType());
}

/* Assuming "cond" represents a simple bound on a loop where the loop
 * iterator "iv" is incremented (or decremented) by one, check if wrapping
 * is possible.
 *
 * Under the given assumptions, wrapping is only possible if "cond" allows
 * for the last value before wrapping, i.e., 2^width - 1 in case of an
 * increasing iterator and 0 in case of a decreasing iterator.
 */
static bool can_wrap(__isl_keep isl_set *cond, ValueDecl *iv, isl_int inc)
{
	bool cw;
	isl_int limit;
	isl_set *test;

	test = isl_set_copy(cond);

	isl_int_init(limit);
	if (isl_int_is_neg(inc))
		isl_int_set_si(limit, 0);
	else {
		isl_int_set_si(limit, 1);
		isl_int_mul_2exp(limit, limit, get_type_size(iv));
		isl_int_sub_ui(limit, limit, 1);
	}

	test = isl_set_fix(cond, isl_dim_set, 0, limit);
	cw = !isl_set_is_empty(test);
	isl_set_free(test);

	isl_int_clear(limit);

	return cw;
}

/* Given a one-dimensional space, construct the following mapping on this
 * space
 *
 *	{ [v] -> [v mod 2^width] }
 *
 * where width is the number of bits used to represent the values
 * of the unsigned variable "iv".
 */
static __isl_give isl_map *compute_wrapping(__isl_take isl_space *dim,
	ValueDecl *iv)
{
	isl_int mod;
	isl_aff *aff;
	isl_map *map;

	isl_int_init(mod);
	isl_int_set_si(mod, 1);
	isl_int_mul_2exp(mod, mod, get_type_size(iv));

	aff = isl_aff_zero_on_domain(isl_local_space_from_space(dim));
	aff = isl_aff_add_coefficient_si(aff, isl_dim_in, 0, 1);
	aff = isl_aff_mod(aff, mod);

	isl_int_clear(mod);

	return isl_map_from_basic_map(isl_basic_map_from_aff(aff));
	map = isl_map_reverse(map);
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
 * If the stride of the loop is not 1, then "i >= init" is replaced by
 *
 *	(exists a: i = init + stride * a and a >= 0)
 *
 * If the loop iterator i is unsigned, then wrapping may occur.
 * During the computation, we work with a virtual iterator that
 * does not wrap.  However, the condition in the code applies
 * to the wrapped value, so we need to change condition(i)
 * into condition([i % 2^width]).
 * After computing the virtual domain and schedule, we apply
 * the function { [v] -> [v % 2^width] } to the domain and the domain
 * of the schedule.  In order not to lose any information, we also
 * need to intersect the domain of the schedule with the virtual domain
 * first, since some iterations in the wrapped domain may be scheduled
 * several times, typically an infinite number of times.
 * Note that there is no need to perform this final wrapping
 * if the loop condition (after wrapping) is simple.
 *
 * Wrapping on unsigned iterators can be avoided entirely if
 * loop condition is simple, the loop iterator is incremented
 * [decremented] by one and the last value before wrapping cannot
 * possibly satisfy the loop condition.
 *
 * Before extracting a pet_scop from the body we remove all
 * assignments in assigned_value to variables that are assigned
 * somewhere in the body of the loop.
 */
struct pet_scop *PetScan::extract_for(ForStmt *stmt)
{
	BinaryOperator *ass;
	Decl *decl;
	Stmt *init;
	Expr *lhs, *rhs;
	ValueDecl *iv;
	isl_space *dim;
	isl_set *domain;
	isl_map *sched;
	isl_set *cond;
	isl_id *id;
	struct pet_scop *scop;
	assigned_value_cache cache(assigned_value);
	isl_int inc;
	bool is_one;
	bool is_unsigned;
	bool is_simple;
	isl_map *wrap = NULL;

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
		lhs = DeclRefExpr::Create(iv->getASTContext(),
			var->getQualifierLoc(), iv, var->getInnerLocStart(),
			var->getType(), VK_LValue);
	} else {
		unsupported(stmt->getInit());
		return NULL;
	}

	isl_int_init(inc);
	if (!check_increment(stmt, iv, inc)) {
		isl_int_clear(inc);
		return NULL;
	}

	is_unsigned = iv->getType()->isUnsignedIntegerType();

	assigned_value.erase(iv);
	clear_assignments clear(assigned_value);
	clear.TraverseStmt(stmt->getBody());

	id = isl_id_alloc(ctx, iv->getName().str().c_str(), iv);

	is_one = isl_int_is_one(inc) || isl_int_is_negone(inc);
	if (is_one)
		domain = extract_comparison(isl_int_is_pos(inc) ? BO_GE : BO_LE,
				lhs, rhs, init);
	else {
		isl_pw_aff *lb = extract_affine(rhs);
		domain = strided_domain(isl_id_copy(id), lb, inc);
	}

	cond = extract_condition(stmt->getCond());
	cond = embed(cond, isl_id_copy(id));
	domain = embed(domain, isl_id_copy(id));
	is_simple = is_simple_bound(cond, inc);
	if (is_unsigned &&
	    (!is_simple || !is_one || can_wrap(cond, iv, inc))) {
		wrap = compute_wrapping(isl_set_get_space(cond), iv);
		cond = isl_set_apply(cond, isl_map_reverse(isl_map_copy(wrap)));
		is_simple = is_simple && is_simple_bound(cond, inc);
	}
	if (!is_simple)
		cond = valid_for_each_iteration(cond,
						isl_set_copy(domain), inc);
	domain = isl_set_intersect(domain, cond);
	domain = isl_set_set_dim_id(domain, isl_dim_set, 0, isl_id_copy(id));
	dim = isl_space_from_domain(isl_set_get_space(domain));
	dim = isl_space_add_dims(dim, isl_dim_out, 1);
	sched = isl_map_universe(dim);
	if (isl_int_is_pos(inc))
		sched = isl_map_equate(sched, isl_dim_in, 0, isl_dim_out, 0);
	else
		sched = isl_map_oppose(sched, isl_dim_in, 0, isl_dim_out, 0);

	if (is_unsigned && !is_simple) {
		wrap = isl_map_set_dim_id(wrap,
					    isl_dim_out, 0, isl_id_copy(id));
		sched = isl_map_intersect_domain(sched, isl_set_copy(domain));
		domain = isl_set_apply(domain, isl_map_copy(wrap));
		sched = isl_map_apply_domain(sched, wrap);
	} else
		isl_map_free(wrap);

	scop = extract(stmt->getBody());
	scop = pet_scop_embed(scop, domain, sched, id);
	assigned_value[iv] = NULL;

	isl_int_clear(inc);
	return scop;
}

struct pet_scop *PetScan::extract(CompoundStmt *stmt)
{
	return extract(stmt->children());
}

/* Look for parameters in any access relation in "expr" that
 * refer to nested accesses.  In particular, these are
 * parameters with no name.
 *
 * If there are any such parameters, then the domain of the access
 * relation, which is still [] at this point, is replaced by
 * [[] -> [t_1,...,t_n]], with n the number of these parameters
 * (after identifying identical nested accesses).
 * The parameters are then equated to the corresponding t dimensions
 * and subsequently projected out.
 * param2pos maps the position of the parameter to the position
 * of the corresponding t dimension.
 */
struct pet_expr *PetScan::resolve_nested(struct pet_expr *expr)
{
	int n;
	int nparam;
	int n_in;
	isl_space *dim;
	isl_map *map;
	std::map<int,int> param2pos;

	if (!expr)
		return expr;

	for (int i = 0; i < expr->n_arg; ++i) {
		expr->args[i] = resolve_nested(expr->args[i]);
		if (!expr->args[i]) {
			pet_expr_free(expr);
			return NULL;
		}
	}

	if (expr->type != pet_expr_access)
		return expr;

	nparam = isl_map_dim(expr->acc.access, isl_dim_param);
	n = 0;
	for (int i = 0; i < nparam; ++i) {
		isl_id *id = isl_map_get_dim_id(expr->acc.access,
						isl_dim_param, i);
		if (id && isl_id_get_user(id) && !isl_id_get_name(id))
			n++;
		isl_id_free(id);
	}

	if (n == 0)
		return expr;

	expr->n_arg = n;
	expr->args = isl_calloc_array(ctx, struct pet_expr *, n);
	if (!expr->args)
		goto error;

	n_in = isl_map_dim(expr->acc.access, isl_dim_in);
	for (int i = 0, pos = 0; i < nparam; ++i) {
		int j;
		isl_id *id = isl_map_get_dim_id(expr->acc.access,
						isl_dim_param, i);
		Expr *nested;

		if (!(id && isl_id_get_user(id) && !isl_id_get_name(id))) {
			isl_id_free(id);
			continue;
		}

		nested = (Expr *) isl_id_get_user(id);
		expr->args[pos] = extract_expr(nested);

		for (j = 0; j < pos; ++j)
			if (pet_expr_is_equal(expr->args[j], expr->args[pos]))
				break;

		if (j < pos) {
			pet_expr_free(expr->args[pos]);
			param2pos[i] = n_in + j;
			n--;
		} else
			param2pos[i] = n_in + pos++;

		isl_id_free(id);
	}
	expr->n_arg = n;

	dim = isl_map_get_space(expr->acc.access);
	dim = isl_space_domain(dim);
	dim = isl_space_from_domain(dim);
	dim = isl_space_add_dims(dim, isl_dim_out, n);
	map = isl_map_universe(dim);
	map = isl_map_domain_map(map);
	map = isl_map_reverse(map);
	expr->acc.access = isl_map_apply_domain(expr->acc.access, map);

	for (int i = nparam - 1; i >= 0; --i) {
		isl_id *id = isl_map_get_dim_id(expr->acc.access,
						isl_dim_param, i);
		if (!(id && isl_id_get_user(id) && !isl_id_get_name(id))) {
			isl_id_free(id);
			continue;
		}

		expr->acc.access = isl_map_equate(expr->acc.access,
					isl_dim_param, i, isl_dim_in,
					param2pos[i]);
		expr->acc.access = isl_map_project_out(expr->acc.access,
					isl_dim_param, i, 1);

		isl_id_free(id);
	}

	return expr;
error:
	pet_expr_free(expr);
	return NULL;
}

/* Convert a top-level pet_expr to a pet_scop with one statement.
 * This mainly involves resolving nested expression parameters
 * and setting the name of the iteration space.
 * The name is given by "label" if it is non-NULL.  Otherwise,
 * it is of the form S_<n_stmt>.
 */
struct pet_scop *PetScan::extract(Stmt *stmt, struct pet_expr *expr,
	__isl_take isl_id *label)
{
	struct pet_stmt *ps;
	SourceLocation loc = stmt->getLocStart();
	int line = PP.getSourceManager().getExpansionLineNumber(loc);

	expr = resolve_nested(expr);
	ps = pet_stmt_from_pet_expr(ctx, line, label, n_stmt++, expr);
	return pet_scop_from_pet_stmt(ctx, ps);
}

/* Check whether "expr" is an affine expression.
 * We turn on autodetection so that we won't generate any warnings
 * and turn off nesting, so that we won't accept any non-affine constructs.
 */
bool PetScan::is_affine(Expr *expr)
{
	isl_pw_aff *pwaff;
	int save_autodetect = autodetect;
	bool save_nesting = nesting_enabled;

	autodetect = 1;
	nesting_enabled = false;

	pwaff = extract_affine(expr);
	isl_pw_aff_free(pwaff);

	autodetect = save_autodetect;
	nesting_enabled = save_nesting;

	return pwaff != NULL;
}

/* Check whether "expr" is an affine constraint.
 * We turn on autodetection so that we won't generate any warnings
 * and turn off nesting, so that we won't accept any non-affine constructs.
 */
bool PetScan::is_affine_condition(Expr *expr)
{
	isl_set *set;
	int save_autodetect = autodetect;
	bool save_nesting = nesting_enabled;

	autodetect = 1;
	nesting_enabled = false;

	set = extract_condition(expr);
	isl_set_free(set);

	autodetect = save_autodetect;
	nesting_enabled = save_nesting;

	return set != NULL;
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
	isl_map *write_then, *write_else;
	isl_set *cond, *comp;
	isl_map *map, *map_true, *map_false;
	int equal;
	struct pet_expr *pe_cond, *pe_then, *pe_else, *pe, *pe_write;
	bool save_nesting = nesting_enabled;

	ass_then = top_assignment_or_null(stmt->getThen());
	ass_else = top_assignment_or_null(stmt->getElse());

	if (!ass_then || !ass_else)
		return NULL;

	if (is_affine_condition(stmt->getCond()))
		return NULL;

	write_then = extract_access(ass_then->getLHS());
	write_else = extract_access(ass_else->getLHS());

	equal = isl_map_is_equal(write_then, write_else);
	isl_map_free(write_else);
	if (equal < 0 || !equal) {
		isl_map_free(write_then);
		return NULL;
	}

	nesting_enabled = allow_nested;
	cond = extract_condition(stmt->getCond());
	nesting_enabled = save_nesting;
	comp = isl_set_complement(isl_set_copy(cond));
	map_true = isl_map_from_domain(isl_set_from_params(isl_set_copy(cond)));
	map_true = isl_map_add_dims(map_true, isl_dim_out, 1);
	map_true = isl_map_fix_si(map_true, isl_dim_out, 0, 1);
	map_false = isl_map_from_domain(isl_set_from_params(isl_set_copy(comp)));
	map_false = isl_map_add_dims(map_false, isl_dim_out, 1);
	map_false = isl_map_fix_si(map_false, isl_dim_out, 0, 0);
	map = isl_map_union_disjoint(map_true, map_false);

	pe_cond = pet_expr_from_access(map);

	pe_then = extract_expr(ass_then->getRHS());
	pe_then = pet_expr_restrict(pe_then, cond);
	pe_else = extract_expr(ass_else->getRHS());
	pe_else = pet_expr_restrict(pe_else, comp);

	pe = pet_expr_new_ternary(ctx, pe_cond, pe_then, pe_else);
	pe_write = pet_expr_from_access(write_then);
	if (pe_write) {
		pe_write->acc.write = 1;
		pe_write->acc.read = 0;
	}
	pe = pet_expr_new_binary(ctx, pet_op_assign, pe_write, pe);
	return extract(stmt, pe);
}

/* Create an access to a virtual array representing the result
 * of a condition.
 * Unlike other accessed data, the id of the array is NULL as
 * there is no ValueDecl in the program corresponding to the virtual
 * array.
 * The array starts out as a scalar, but grows along with the
 * statement writing to the array in pet_scop_embed.
 */
static __isl_give isl_map *create_test_access(isl_ctx *ctx, int test_nr)
{
	isl_space *dim = isl_space_alloc(ctx, 0, 0, 0);
	isl_id *id;
	char name[50];

	snprintf(name, sizeof(name), "__pet_test_%d", test_nr);
	id = isl_id_alloc(ctx, name, NULL);
	dim = isl_space_set_tuple_id(dim, isl_dim_out, id);
	return isl_map_universe(dim);
}

/* Create a pet_scop with a single statement evaluating "cond"
 * and writing the result to a virtual scalar, as expressed by
 * "access".
 */
struct pet_scop *PetScan::extract_non_affine_condition(Expr *cond,
	__isl_take isl_map *access)
{
	struct pet_expr *expr, *write;
	struct pet_stmt *ps;
	SourceLocation loc = cond->getLocStart();
	int line = PP.getSourceManager().getExpansionLineNumber(loc);

	write = pet_expr_from_access(access);
	if (write) {
		write->acc.write = 1;
		write->acc.read = 0;
	}
	expr = extract_expr(cond);
	expr = pet_expr_new_binary(ctx, pet_op_assign, write, expr);
	ps = pet_stmt_from_pet_expr(ctx, line, NULL, n_stmt++, expr);
	return pet_scop_from_pet_stmt(ctx, ps);
}

/* Add an array with the given extend ("access") to the list
 * of arrays in "scop" and return the extended pet_scop.
 * The array is marked as attaining values 0 and 1 only.
 */
static struct pet_scop *scop_add_array(struct pet_scop *scop,
	__isl_keep isl_map *access)
{
	isl_ctx *ctx = isl_map_get_ctx(access);
	isl_space *dim;
	struct pet_array **arrays;
	struct pet_array *array;

	if (!scop)
		return NULL;
	if (!ctx)
		goto error;

	arrays = isl_realloc_array(ctx, scop->arrays, struct pet_array *,
				    scop->n_array + 1);
	if (!arrays)
		goto error;
	scop->arrays = arrays;

	array = isl_calloc_type(ctx, struct pet_array);
	if (!array)
		goto error;

	array->extent = isl_map_range(isl_map_copy(access));
	dim = isl_space_params_alloc(ctx, 0);
	array->context = isl_set_universe(dim);
	dim = isl_space_set_alloc(ctx, 0, 1);
	array->value_bounds = isl_set_universe(dim);
	array->value_bounds = isl_set_lower_bound_si(array->value_bounds,
						isl_dim_set, 0, 0);
	array->value_bounds = isl_set_upper_bound_si(array->value_bounds,
						isl_dim_set, 0, 1);
	array->element_type = strdup("int");

	scop->arrays[scop->n_array] = array;
	scop->n_array++;

	if (!array->extent || !array->context)
		goto error;

	return scop;
error:
	pet_scop_free(scop);
	return NULL;
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
 *
 * If the condition is not-affine, then we create a separate
 * statement that write the result of the condition to a virtual scalar.
 * A constraint requiring the value of this virtual scalar to be one
 * is added to the iteration domains of the then branch.
 * Similarly, a constraint requiring the value of this virtual scalar
 * to be zero is added to the iteration domains of the else branch, if any.
 * We adjust the schedules to ensure that the virtual scalar is written
 * before it is read.
 */
struct pet_scop *PetScan::extract(IfStmt *stmt)
{
	struct pet_scop *scop_then, *scop_else, *scop;
	assigned_value_cache cache(assigned_value);
	isl_map *test_access = NULL;

	scop = extract_conditional_assignment(stmt);
	if (scop)
		return scop;

	if (allow_nested && !is_affine_condition(stmt->getCond())) {
		test_access = create_test_access(ctx, n_test++);
		scop = extract_non_affine_condition(stmt->getCond(),
						    isl_map_copy(test_access));
		scop = scop_add_array(scop, test_access);
		if (!scop) {
			isl_map_free(test_access);
			return NULL;
		}
	}

	scop_then = extract(stmt->getThen());

	if (stmt->getElse()) {
		scop_else = extract(stmt->getElse());
		if (autodetect) {
			if (scop_then && !scop_else) {
				partial = true;
				pet_scop_free(scop);
				isl_map_free(test_access);
				return scop_then;
			}
			if (!scop_then && scop_else) {
				partial = true;
				pet_scop_free(scop);
				isl_map_free(test_access);
				return scop_else;
			}
		}
	}

	if (!scop) {
		isl_set *cond;
		cond = extract_condition(stmt->getCond());
		scop = pet_scop_restrict(scop_then, isl_set_copy(cond));

		if (stmt->getElse()) {
			cond = isl_set_complement(cond);
			scop_else = pet_scop_restrict(scop_else, cond);
			scop = pet_scop_add(ctx, scop, scop_else);
		} else
			isl_set_free(cond);
	} else {
		scop = pet_scop_prefix(scop, 0);
		scop_then = pet_scop_prefix(scop_then, 1);
		scop_then = pet_scop_filter(scop_then,
						isl_map_copy(test_access), 1);
		scop = pet_scop_add(ctx, scop, scop_then);
		if (stmt->getElse()) {
			scop_else = pet_scop_prefix(scop_else, 1);
			scop_else = pet_scop_filter(scop_else, test_access, 0);
			scop = pet_scop_add(ctx, scop, scop_else);
		} else
			isl_map_free(test_access);
	}

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

/* Try and construct a pet_scop corresponding to "stmt".
 */
struct pet_scop *PetScan::extract(Stmt *stmt)
{
	if (isa<Expr>(stmt))
		return extract(stmt, extract_expr(cast<Expr>(stmt)));

	switch (stmt->getStmtClass()) {
	case Stmt::WhileStmtClass:
		return extract(cast<WhileStmt>(stmt));
	case Stmt::ForStmtClass:
		return extract_for(cast<ForStmt>(stmt));
	case Stmt::IfStmtClass:
		return extract(cast<IfStmt>(stmt));
	case Stmt::CompoundStmtClass:
		return extract(cast<CompoundStmt>(stmt));
	case Stmt::LabelStmtClass:
		return extract(cast<LabelStmt>(stmt));
	default:
		unsupported(stmt);
	}

	return NULL;
}

/* Try and construct a pet_scop corresponding to (part of)
 * a sequence of statements.
 */
struct pet_scop *PetScan::extract(StmtRange stmt_range)
{
	pet_scop *scop;
	StmtIterator i;
	int j;
	bool partial_range = false;

	scop = pet_scop_empty(ctx);
	for (i = stmt_range.first, j = 0; i != stmt_range.second; ++i, ++j) {
		Stmt *child = *i;
		struct pet_scop *scop_i;
		scop_i = extract(child);
		if (scop && partial) {
			pet_scop_free(scop_i);
			break;
		}
		scop_i = pet_scop_prefix(scop_i, j);
		if (autodetect) {
			if (scop_i)
				scop = pet_scop_add(ctx, scop, scop_i);
			else
				partial_range = true;
			if (scop->n_stmt != 0 && !scop_i)
				partial = true;
		} else {
			scop = pet_scop_add(ctx, scop, scop_i);
		}
		if (partial)
			break;
	}

	if (scop && partial_range)
		partial = true;

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

	start_off = SM.getFileOffset(stmt->getLocStart());
	end_off = SM.getFileOffset(stmt->getLocEnd());

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
		start_off = SM.getFileOffset(child->getLocStart());
		end_off = SM.getFileOffset(child->getLocEnd());
		if (start_off < loc.start && end_off > loc.end)
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

	return extract(StmtRange(start, end));
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

/* Construct and return a pet_array corresponding to the variable "decl".
 * In particular, initialize array->extent to
 *
 *	{ name[i_1,...,i_d] : i_1,...,i_d >= 0 }
 *
 * and then call set_upper_bounds to set the upper bounds on the indices
 * based on the type of the variable.
 */
struct pet_array *PetScan::extract_array(isl_ctx *ctx, ValueDecl *decl)
{
	struct pet_array *array;
	QualType qt = decl->getType();
	const Type *type = qt.getTypePtr();
	int depth = array_depth(type);
	QualType base = base_type(qt);
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
	array->element_type = strdup(name.c_str());

	return array;
}

/* Construct a list of pet_arrays, one for each array (or scalar)
 * accessed inside "scop" add this list to "scop" and return the result.
 *
 * The context of "scop" is updated with the intesection of
 * the contexts of all arrays, i.e., constraints on the parameters
 * that ensure that the arrays have a valid (non-negative) size.
 */
struct pet_scop *PetScan::scan_arrays(struct pet_scop *scop)
{
	int i;
	set<ValueDecl *> arrays;
	set<ValueDecl *>::iterator it;
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
		scop->arrays[n_array + i] = array = extract_array(ctx, *it);
		if (!scop->arrays[n_array + i])
			goto error;
		scop->n_array++;
		scop->context = isl_set_intersect(scop->context,
						isl_set_copy(array->context));
		if (!scop->context)
			goto error;
	}

	return scop;
error:
	pet_scop_free(scop);
	return NULL;
}

/* Construct a pet_scop from the given function.
 */
struct pet_scop *PetScan::scan(FunctionDecl *fd)
{
	pet_scop *scop;
	Stmt *stmt;

	stmt = fd->getBody();

	if (autodetect)
		scop = extract(stmt);
	else
		scop = scan(stmt);
	scop = pet_scop_detect_parameter_accesses(scop);
	scop = scan_arrays(scop);

	return scop;
}
