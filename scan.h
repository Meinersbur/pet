#include <map>

#include <clang/Basic/SourceManager.h>
#include <clang/AST/Decl.h>
#include <clang/AST/Stmt.h>
#include <clang/Lex/Preprocessor.h>

#include <isl/ctx.h>
#include <isl/map.h>

#include "scop.h"

/* The location of the scop, as delimited by scop and endscop
 * pragmas by the user.
 */
struct ScopLoc {
	ScopLoc() : end(0) {}

	unsigned start;
	unsigned end;
};

struct PetScan {
	clang::Preprocessor &PP;
	/* If autodetect is false, then loc contains the location
	 * of the scop to be extracted.
	 */
	ScopLoc &loc;
	isl_ctx *ctx;
	/* The sequence number of the next statement. */
	int n_stmt;
	/* If autodetect is false, a scop delimited by pragmas is extracted,
	 * otherwise we take any scop that we can find.
	 */
	bool autodetect;
	/* Set if the pet_scop returned by an extract method only
	 * represents part of the input tree.
	 */
	bool partial;
	/* Set is nested accesses are allowed in general.
	 * This currently defaults to true.
	 */
	bool allow_nested;
	/* Set if nested accesses are allowed in that part of the tree
	 * that is currently under investigation.
	 */
	bool nesting_enabled;
	/* Maps identifiers to the last expression that was assigned to them.
	 * If an identifier is mapped to NULL, then something may have
	 * been assigned, but we don't know what.
	 */
	std::map<clang::ValueDecl *, clang::Expr *> assigned_value;

	PetScan(isl_ctx *ctx, clang::Preprocessor &PP, ScopLoc &loc,
		int autodetect) :
		ctx(ctx), PP(PP), loc(loc), autodetect(autodetect),
		n_stmt(0), partial(0), allow_nested(true),
		nesting_enabled(false) { }

	struct pet_scop *scan(clang::FunctionDecl *fd);
private:
	struct pet_scop *scan(clang::Stmt *stmt);

	struct pet_scop *scan_arrays(struct pet_scop *scop);
	struct pet_array *extract_array(isl_ctx *ctx, clang::ValueDecl *decl);
	struct pet_array *set_upper_bounds(struct pet_array *array,
		const clang::Type *type, int pos);

	struct pet_scop *extract_conditional_assignment(clang::IfStmt *stmt);

	struct pet_scop *extract(clang::Stmt *stmt);
	struct pet_scop *extract(clang::StmtRange stmt_range);
	struct pet_scop *extract(clang::IfStmt *stmt);
	struct pet_scop *extract(clang::CompoundStmt *stmt);

	struct pet_scop *extract(clang::Stmt *stmt, struct pet_expr *expr);

	clang::BinaryOperator *extract_initialization(clang::ForStmt *stmt);
	clang::ValueDecl *extract_induction_variable(clang::BinaryOperator *stmt);
	bool check_unary_increment(clang::UnaryOperator *op,
				clang::ValueDecl *iv, isl_int &inc);
	bool check_binary_increment(clang::BinaryOperator *op,
				clang::ValueDecl *iv, isl_int &inc);
	bool check_compound_increment(clang::CompoundAssignOperator *op,
				clang::ValueDecl *iv, isl_int &inc);
	bool check_increment(clang::ForStmt *stmt, clang::ValueDecl *iv,
				isl_int &inc);
	struct pet_scop *extract_for(clang::ForStmt *stmt);
	struct pet_scop *extract_infinite_for(clang::ForStmt *stmt);

	struct pet_expr *extract_expr(clang::Expr *expr);
	struct pet_expr *extract_expr(clang::UnaryOperator *expr);
	struct pet_expr *extract_expr(clang::BinaryOperator *expr);
	struct pet_expr *extract_expr(clang::ImplicitCastExpr *expr);
	struct pet_expr *extract_expr(clang::FloatingLiteral *expr);
	struct pet_expr *extract_expr(clang::ParenExpr *expr);
	struct pet_expr *extract_expr(clang::ConditionalOperator *expr);
	struct pet_expr *extract_expr(clang::CallExpr *expr);

	struct pet_expr *resolve_nested(struct pet_expr *expr);
	struct pet_expr *extract_access_expr(clang::Expr *expr);

	__isl_give isl_map *extract_access(clang::ArraySubscriptExpr *expr);
	__isl_give isl_map *extract_access(clang::Expr *expr);
	__isl_give isl_map *extract_access(clang::ImplicitCastExpr *expr);
	__isl_give isl_map *extract_access(clang::DeclRefExpr *expr);
	__isl_give isl_map *extract_access(clang::IntegerLiteral *expr);

	__isl_give isl_pw_aff *extract_affine_div(clang::BinaryOperator *expr);
	__isl_give isl_pw_aff *extract_affine_mod(clang::BinaryOperator *expr);
	__isl_give isl_pw_aff *extract_affine_mul(clang::BinaryOperator *expr);

	int extract_int(clang::IntegerLiteral *expr, isl_int *v);

	isl_pw_aff *non_affine(clang::Expr *expr);

	bool is_affine(clang::Expr *expr);
	bool is_affine_condition(clang::Expr *expr);

	__isl_give isl_pw_aff *extract_affine(const llvm::APInt &val);
	__isl_give isl_pw_aff *extract_affine(clang::Expr *expr);
	__isl_give isl_pw_aff *extract_affine(clang::IntegerLiteral *expr);
	__isl_give isl_pw_aff *extract_affine(clang::ImplicitCastExpr *expr);
	__isl_give isl_pw_aff *extract_affine(clang::DeclRefExpr *expr);
	__isl_give isl_pw_aff *extract_affine(clang::BinaryOperator *expr);
	__isl_give isl_pw_aff *extract_affine(clang::UnaryOperator *expr);
	__isl_give isl_pw_aff *extract_affine(clang::ParenExpr *expr);
	__isl_give isl_pw_aff *extract_affine(clang::CallExpr *expr);
	__isl_give isl_pw_aff *extract_affine(clang::ArraySubscriptExpr *expr);
	__isl_give isl_pw_aff *extract_affine(clang::ConditionalOperator *expr);

	__isl_give isl_set *extract_implicit_condition(clang::Expr *expr);

	__isl_give isl_set *extract_condition(clang::UnaryOperator *expr);
	__isl_give isl_set *extract_condition(clang::Expr *expr);
	__isl_give isl_set *extract_comparison(clang::BinaryOperator *expr);
	__isl_give isl_set *extract_comparison(clang::BinaryOperatorKind op,
		clang::Expr *LHS, clang::Expr *RHS, clang::Expr *comp);
	__isl_give isl_set *extract_boolean(clang::BinaryOperator *expr);
	__isl_give isl_set *extract_boolean(clang::UnaryOperator *expr);

	void unsupported(clang::Stmt *stmt);
};
