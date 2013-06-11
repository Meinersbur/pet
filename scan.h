#include <map>

#include <clang/Basic/SourceManager.h>
#include <clang/AST/Decl.h>
#include <clang/AST/Stmt.h>
#include <clang/Lex/Preprocessor.h>

#include <isl/ctx.h>
#include <isl/map.h>
#include <isl/val.h>

#include "scop.h"

/* The location of the scop, as delimited by scop and endscop
 * pragmas by the user.
 */
struct ScopLoc {
	ScopLoc() : end(0) {}

	unsigned start;
	unsigned end;
};

/* Compare two RecordDecl pointers based on their names.
 */
struct less_name {
	bool operator()(const clang::RecordDecl *x,
			const clang::RecordDecl *y) {
		return x->getNameAsString().compare(y->getNameAsString()) < 0;
	}
};

/* A sorted set of RecordDecl pointers.  The actual order is not important,
 * only that it is consistent across platforms.
 */
typedef std::set<clang::RecordDecl *, less_name> lex_recorddecl_set;

struct PetScan {
	clang::Preprocessor &PP;
	clang::ASTContext &ast_context;
	/* If autodetect is false, then loc contains the location
	 * of the scop to be extracted.
	 */
	ScopLoc &loc;
	isl_ctx *ctx;
	pet_options *options;
	/* The sequence number of the next statement. */
	int n_stmt;
	/* The sequence number of the next virtual scalar. */
	int n_test;
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
	/* Maps identifiers to the last value that was assigned to them.
	 * If an identifier is mapped to NULL, then something may have
	 * been assigned, but we don't know what.
	 * assigned_value does not take a reference to the isl_pw_aff
	 * object, so each such isl_pw_aff needs to be stored in
	 * the set of "expressions".
	 */
	std::map<clang::ValueDecl *, isl_pw_aff *> assigned_value;
	/* A collection of isl_pw_affs used in assigned_value or other
	 * temporary maps.  expressions holds a reference for each
	 * isl_pw_aff, which is freed in the destructor of PetScan.
	 */
	std::set<isl_pw_aff *> expressions;

	/* A union of mappings of the form
	 *	{ identifier[] -> [i] : lower_bound <= i <= upper_bound }
	 */
	isl_union_map *value_bounds;

	PetScan(clang::Preprocessor &PP,
		clang::ASTContext &ast_context, ScopLoc &loc,
		pet_options *options, __isl_take isl_union_map *value_bounds) :
		ctx(isl_union_map_get_ctx(value_bounds)), PP(PP),
		ast_context(ast_context), loc(loc),
		options(options), value_bounds(value_bounds),
		n_stmt(0), n_test(0), partial(0), allow_nested(true),
		nesting_enabled(false) { }

	~PetScan();

	struct pet_scop *scan(clang::FunctionDecl *fd);

	static __isl_give isl_val *extract_int(isl_ctx *ctx,
		clang::IntegerLiteral *expr);
	static __isl_give isl_val *extract_unsigned(isl_ctx *ctx,
		const llvm::APInt &val);
private:
	void assign(struct pet_expr *lhs, clang::Expr *rhs);

	__isl_give isl_pw_aff *signed_overflow(__isl_take isl_pw_aff *pa,
		unsigned width);
	void insert_expression(__isl_take isl_pw_aff *expr);
	struct pet_scop *scan(clang::Stmt *stmt);

	struct pet_scop *scan_arrays(struct pet_scop *scop);
	struct pet_array *extract_array(isl_ctx *ctx, clang::ValueDecl *decl,
		lex_recorddecl_set *types);
	struct pet_array *extract_array(isl_ctx *ctx,
		std::vector<clang::ValueDecl *> decls,
		lex_recorddecl_set *types);
	struct pet_array *set_upper_bounds(struct pet_array *array,
		const clang::Type *type, int pos);

	struct pet_scop *extract_non_affine_condition(clang::Expr *cond,
		int stmt_nr, __isl_take isl_multi_pw_aff *index);

	struct pet_scop *extract_conditional_assignment(clang::IfStmt *stmt);
	struct pet_scop *extract_non_affine_if(clang::Expr *cond,
		struct pet_scop *scop_then, struct pet_scop *scop_else,
		bool have_else, int stmt_id);

	struct pet_scop *kill(clang::Stmt *stmt, struct pet_array *array);

	struct pet_scop *extract(clang::Stmt *stmt,
		bool skip_declarations = false);
	struct pet_scop *extract(clang::StmtRange stmt_range, bool block,
		bool skip_declarations);
	struct pet_scop *extract(clang::IfStmt *stmt);
	struct pet_scop *extract(clang::WhileStmt *stmt);
	struct pet_scop *extract(clang::CompoundStmt *stmt,
		bool skip_declarations = false);
	struct pet_scop *extract(clang::LabelStmt *stmt);
	struct pet_scop *extract(clang::ContinueStmt *stmt);
	struct pet_scop *extract(clang::BreakStmt *stmt);
	struct pet_scop *extract(clang::DeclStmt *expr);

	struct pet_scop *update_scop_start_end(struct pet_scop *scop,
		clang::SourceRange range, bool skip_semi);
	struct pet_scop *extract(clang::Stmt *stmt, struct pet_expr *expr,
				__isl_take isl_id *label = NULL);
	struct pet_stmt *extract_kill(struct pet_scop *scop);

	clang::BinaryOperator *initialization_assignment(clang::Stmt *init);
	clang::Decl *initialization_declaration(clang::Stmt *init);
	clang::ValueDecl *extract_induction_variable(clang::BinaryOperator *stmt);
	clang::VarDecl *extract_induction_variable(clang::Stmt *init,
				clang::Decl *stmt);
	__isl_give isl_pw_aff *extract_unary_increment(clang::UnaryOperator *op,
				clang::ValueDecl *iv);
	__isl_give isl_pw_aff *extract_binary_increment(
				clang::BinaryOperator *op,
				clang::ValueDecl *iv);
	__isl_give isl_pw_aff *extract_compound_increment(
				clang::CompoundAssignOperator *op,
				clang::ValueDecl *iv);
	__isl_give isl_pw_aff *extract_increment(clang::ForStmt *stmt,
				clang::ValueDecl *iv);
	struct pet_scop *extract_for(clang::ForStmt *stmt);
	struct pet_scop *extract_infinite_loop(clang::Stmt *body);
	struct pet_scop *extract_infinite_for(clang::ForStmt *stmt);
	struct pet_scop *extract_affine_while(__isl_take isl_pw_aff *pa,
				clang::Stmt *body);

	void mark_write(struct pet_expr *access);
	struct pet_expr *extract_assume(clang::Expr *expr);
	struct pet_expr *extract_argument(clang::FunctionDecl *fd, int pos,
		clang::Expr *expr);
	struct pet_expr *extract_expr(clang::Expr *expr);
	struct pet_expr *extract_expr(clang::UnaryOperator *expr);
	struct pet_expr *extract_expr(clang::BinaryOperator *expr);
	struct pet_expr *extract_expr(clang::ImplicitCastExpr *expr);
	struct pet_expr *extract_expr(clang::IntegerLiteral *expr);
	struct pet_expr *extract_expr(clang::FloatingLiteral *expr);
	struct pet_expr *extract_expr(clang::ParenExpr *expr);
	struct pet_expr *extract_expr(clang::ConditionalOperator *expr);
	struct pet_expr *extract_expr(clang::CallExpr *expr);
	struct pet_expr *extract_expr(clang::CStyleCastExpr *expr);

	int extract_nested(__isl_keep isl_space *space,
		int n_arg, struct pet_expr **args,
		std::map<int,int> &param2pos);
	struct pet_expr *extract_nested(struct pet_expr *expr, int n,
		std::map<int,int> &param2pos);
	struct pet_stmt *extract_nested(struct pet_stmt *stmt, int n,
		std::map<int,int> &param2pos);
	struct pet_expr *resolve_nested(struct pet_expr *expr);
	struct pet_scop *resolve_nested(struct pet_scop *scop);
	struct pet_stmt *resolve_nested(struct pet_stmt *stmt);
	struct pet_expr *extract_access_expr(clang::Expr *expr);
	struct pet_expr *extract_access_expr(clang::ValueDecl *decl);

	__isl_give isl_multi_pw_aff *extract_index(
		clang::ArraySubscriptExpr *expr);
	__isl_give isl_multi_pw_aff *extract_index(clang::Expr *expr);
	__isl_give isl_multi_pw_aff *extract_index(
		clang::ImplicitCastExpr *expr);
	__isl_give isl_multi_pw_aff *extract_index(clang::DeclRefExpr *expr);
	__isl_give isl_multi_pw_aff *extract_index(clang::ValueDecl *decl);
	__isl_give isl_multi_pw_aff *extract_index(
		clang::IntegerLiteral *expr);
	__isl_give isl_multi_pw_aff *extract_index(clang::MemberExpr *expr);

	__isl_give isl_val *extract_int(clang::Expr *expr);
	__isl_give isl_val *extract_int(clang::ParenExpr *expr);

	__isl_give isl_pw_aff *extract_affine_add(clang::BinaryOperator *expr);
	__isl_give isl_pw_aff *extract_affine_div(clang::BinaryOperator *expr);
	__isl_give isl_pw_aff *extract_affine_mod(clang::BinaryOperator *expr);
	__isl_give isl_pw_aff *extract_affine_mul(clang::BinaryOperator *expr);

	isl_pw_aff *nested_access(clang::Expr *expr);

	__isl_give isl_pw_aff *try_extract_affine(clang::Expr *expr);
	__isl_give isl_pw_aff *try_extract_affine_condition(clang::Expr *expr);
	bool is_affine_condition(clang::Expr *expr);
	__isl_give isl_pw_aff *try_extract_nested_condition(clang::Expr *expr);
	bool is_nested_allowed(__isl_keep isl_pw_aff *pa, pet_scop *scop);

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
	__isl_give isl_pw_aff *extract_affine(clang::MemberExpr *expr);
	__isl_give isl_pw_aff *extract_affine(clang::ConditionalOperator *expr);

	__isl_give isl_pw_aff *extract_implicit_condition(clang::Expr *expr);

	__isl_give isl_pw_aff *extract_condition(clang::UnaryOperator *expr);
	__isl_give isl_pw_aff *extract_condition(clang::Expr *expr);
	__isl_give isl_pw_aff *extract_comparison(clang::BinaryOperator *expr);
	__isl_give isl_pw_aff *extract_comparison(clang::BinaryOperatorKind op,
		clang::Expr *LHS, clang::Expr *RHS, clang::Stmt *comp);
	__isl_give isl_pw_aff *extract_boolean(clang::BinaryOperator *expr);
	__isl_give isl_pw_aff *extract_boolean(clang::UnaryOperator *expr);

	void report(clang::Stmt *stmt, unsigned id);
	void unsupported(clang::Stmt *stmt);
	void report_prototype_required(clang::Stmt *stmt);
	void report_missing_increment(clang::Stmt *stmt);
};
