#include <map>

#include <clang/Basic/SourceManager.h>
#include <clang/AST/Decl.h>
#include <clang/AST/Stmt.h>
#include <clang/Lex/Preprocessor.h>

#include <isl/ctx.h>
#include <isl/map.h>
#include <isl/val.h>

#include "context.h"
#include "loc.h"
#include "scop.h"
#include "summary.h"
#include "tree.h"

/* The location of the scop, as delimited by scop and endscop
 * pragmas by the user.
 * "start_line" is the line number of the start position.
 */
struct ScopLoc {
	ScopLoc() : end(0) {}

	unsigned start_line;
	unsigned start;
	unsigned end;
};

/* The information extracted from a pragma pencil independent.
 * We currently only keep track of the line number where
 * the pragma appears.
 */
struct Independent {
	Independent(unsigned line) : line(line) {}

	unsigned line;
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
	/* Set if the pet_scop returned by an extract method only
	 * represents part of the input tree.
	 */
	bool partial;

	/* A cache of size expressions for array types as computed
	 * by PetScan::get_array_size.
	 */
	std::map<const clang::Type *, pet_expr *> type_size;

	/* A cache of funtion summaries for function declarations
	 * as extracted by PetScan::get_summary.
	 */
	std::map<clang::FunctionDecl *, pet_function_summary *> summary_cache;

	/* A union of mappings of the form
	 *	{ identifier[] -> [i] : lower_bound <= i <= upper_bound }
	 */
	isl_union_map *value_bounds;

	/* The line number of the previously considered Stmt. */
	unsigned last_line;
	/* The line number of the Stmt currently being considered. */
	unsigned current_line;
	/* Information about the independent pragmas in the source code. */
	std::vector<Independent> &independent;

	PetScan(clang::Preprocessor &PP,
		clang::ASTContext &ast_context, ScopLoc &loc,
		pet_options *options, __isl_take isl_union_map *value_bounds,
		std::vector<Independent> &independent) :
		ctx(isl_union_map_get_ctx(value_bounds)), PP(PP),
		ast_context(ast_context), loc(loc),
		options(options), value_bounds(value_bounds),
		partial(false), last_line(0), current_line(0),
		independent(independent) { }

	~PetScan();

	struct pet_scop *scan(clang::FunctionDecl *fd);

	static __isl_give isl_val *extract_int(isl_ctx *ctx,
		clang::IntegerLiteral *expr);
	__isl_give pet_expr *get_array_size(const clang::Type *type);
	struct pet_array *extract_array(isl_ctx *ctx, clang::ValueDecl *decl,
		lex_recorddecl_set *types, __isl_keep pet_context *pc);
private:
	void set_current_stmt(clang::Stmt *stmt);
	bool is_current_stmt_marked_independent();

	struct pet_scop *scan(clang::Stmt *stmt);

	struct pet_scop *scan_arrays(struct pet_scop *scop,
		__isl_keep pet_context *pc);
	struct pet_array *extract_array(isl_ctx *ctx,
		std::vector<clang::ValueDecl *> decls,
		lex_recorddecl_set *types, __isl_keep pet_context *pc);
	__isl_give pet_expr *set_upper_bounds(__isl_take pet_expr *expr,
		const clang::Type *type, int pos);
	struct pet_array *set_upper_bounds(struct pet_array *array,
		const clang::Type *type, __isl_keep pet_context *pc);

	__isl_give pet_tree *extract(clang::Stmt *stmt,
		bool skip_declarations = false);
	__isl_give pet_tree *extract(clang::StmtRange stmt_range, bool block,
		bool skip_declarations);
	__isl_give pet_tree *extract(clang::IfStmt *stmt);
	__isl_give pet_tree *extract(clang::WhileStmt *stmt);
	__isl_give pet_tree *extract(clang::CompoundStmt *stmt,
		bool skip_declarations = false);
	__isl_give pet_tree *extract(clang::LabelStmt *stmt);
	__isl_give pet_tree *extract(clang::DeclStmt *expr);

	__isl_give pet_loc *construct_pet_loc(clang::SourceRange range,
		bool skip_semi);
	__isl_give pet_tree *extract(__isl_take pet_expr *expr,
		clang::SourceRange range, bool skip_semi);
	__isl_give pet_tree *update_loc(__isl_take pet_tree *tree,
		clang::Stmt *stmt);

	struct pet_scop *extract_scop(__isl_take pet_tree *tree);

	clang::BinaryOperator *initialization_assignment(clang::Stmt *init);
	clang::Decl *initialization_declaration(clang::Stmt *init);
	clang::ValueDecl *extract_induction_variable(clang::BinaryOperator *stmt);
	clang::VarDecl *extract_induction_variable(clang::Stmt *init,
				clang::Decl *stmt);
	__isl_give pet_expr *extract_unary_increment(clang::UnaryOperator *op,
				clang::ValueDecl *iv);
	__isl_give pet_expr *extract_binary_increment(
				clang::BinaryOperator *op,
				clang::ValueDecl *iv);
	__isl_give pet_expr *extract_compound_increment(
				clang::CompoundAssignOperator *op,
				clang::ValueDecl *iv);
	__isl_give pet_expr *extract_increment(clang::ForStmt *stmt,
				clang::ValueDecl *iv);
	__isl_give pet_tree *extract_for(clang::ForStmt *stmt);

	__isl_give pet_expr *extract_assume(clang::Expr *expr);
	__isl_give pet_function_summary *get_summary(clang::FunctionDecl *fd);
	__isl_give pet_expr *set_summary(__isl_take pet_expr *expr,
		clang::FunctionDecl *fd);
	__isl_give pet_expr *extract_argument(clang::FunctionDecl *fd, int pos,
		clang::Expr *expr);
	__isl_give pet_expr *extract_expr(const llvm::APInt &val);
	__isl_give pet_expr *extract_expr(clang::Expr *expr);
	__isl_give pet_expr *extract_expr(clang::UnaryOperator *expr);
	__isl_give pet_expr *extract_expr(clang::BinaryOperator *expr);
	__isl_give pet_expr *extract_expr(clang::ImplicitCastExpr *expr);
	__isl_give pet_expr *extract_expr(clang::IntegerLiteral *expr);
	__isl_give pet_expr *extract_expr(clang::EnumConstantDecl *expr);
	__isl_give pet_expr *extract_expr(clang::FloatingLiteral *expr);
	__isl_give pet_expr *extract_expr(clang::ParenExpr *expr);
	__isl_give pet_expr *extract_expr(clang::ConditionalOperator *expr);
	__isl_give pet_expr *extract_expr(clang::CallExpr *expr);
	__isl_give pet_expr *extract_expr(clang::CStyleCastExpr *expr);

	__isl_give pet_expr *extract_access_expr(clang::QualType qt,
		__isl_take pet_expr *index);
	__isl_give pet_expr *extract_access_expr(clang::Expr *expr);
	__isl_give pet_expr *extract_access_expr(clang::ValueDecl *decl);

	__isl_give pet_expr *extract_index_expr(
		clang::ArraySubscriptExpr *expr);
	__isl_give pet_expr *extract_index_expr(clang::Expr *expr);
	__isl_give pet_expr *extract_index_expr(clang::ImplicitCastExpr *expr);
	__isl_give pet_expr *extract_index_expr(clang::DeclRefExpr *expr);
	__isl_give pet_expr *extract_index_expr(clang::ValueDecl *decl);
	__isl_give pet_expr *extract_index_expr(clang::MemberExpr *expr);

	__isl_give isl_val *extract_int(clang::Expr *expr);
	__isl_give isl_val *extract_int(clang::ParenExpr *expr);

	void report(clang::Stmt *stmt, unsigned id);
	void unsupported(clang::Stmt *stmt);
	void report_prototype_required(clang::Stmt *stmt);
	void report_missing_increment(clang::Stmt *stmt);
};
