#ifndef PET_H
#define PET_H

#include <isl/aff.h>
#include <isl/arg.h>
#include <isl/ast_build.h>
#include <isl/set.h>
#include <isl/map.h>
#include <isl/union_map.h>
#include <isl/printer.h>
#include <isl/id_to_ast_expr.h>

#if defined(__cplusplus)
extern "C" {
#endif

struct pet_options;
ISL_ARG_DECL(pet_options, struct pet_options, pet_options_args)

/* If autodetect is set, any valid scop is extracted.
 * Otherwise, the scop needs to be delimited by pragmas.
 */
int pet_options_set_autodetect(isl_ctx *ctx, int val);
int pet_options_get_autodetect(isl_ctx *ctx);

#define	PET_OVERFLOW_AVOID	0
#define	PET_OVERFLOW_IGNORE	1
int pet_options_set_signed_overflow(isl_ctx *ctx, int val);
int pet_options_get_signed_overflow(isl_ctx *ctx);

enum pet_expr_type {
	pet_expr_access,
	pet_expr_call,
	pet_expr_cast,
	pet_expr_double,
	pet_expr_unary,
	pet_expr_binary,
	pet_expr_ternary
};

enum pet_op_type {
	/* only compound assignments operators before assignment */
	pet_op_add_assign,
	pet_op_sub_assign,
	pet_op_mul_assign,
	pet_op_div_assign,
	pet_op_assign,
	pet_op_add,
	pet_op_sub,
	pet_op_mul,
	pet_op_div,
	pet_op_mod,
	pet_op_eq,
	pet_op_le,
	pet_op_lt,
	pet_op_gt,
	pet_op_minus,
	pet_op_post_inc,
	pet_op_post_dec,
	pet_op_pre_inc,
	pet_op_pre_dec,
	pet_op_address_of,
	pet_op_kill,
	pet_op_last
};

/* Index into the pet_expr->args array when pet_expr->type == pet_expr_unary
 */
enum pet_un_arg_type {
	pet_un_arg
};

/* Indices into the pet_expr->args array when
 * pet_expr->type == pet_expr_binary
 */
enum pet_bin_arg_type {
	pet_bin_lhs,
	pet_bin_rhs
};

/* Indices into the pet_expr->args array when
 * pet_expr->type == pet_expr_ternary
 */
enum pet_ter_arg_type {
	pet_ter_cond,
	pet_ter_true,
	pet_ter_false
};

/* d is valid when type == pet_expr_double
 * acc is valid when type == pet_expr_access
 * name is valid when type == pet_expr_call
 * type is valid when type == pet_expr_cast
 * op is valid otherwise
 *
 * For each access expression inside the body of a statement, acc.ref_id
 * is a unique reference identifier.
 * acc.index represents the index expression, while acc.access
 * represents the corresponding access relation.
 * The output dimension of the index expression may be smaller
 * than the number of dimensions of the accessed array.
 * The target space of the access relation, on the other hand,
 * is equal to the array space.
 * Both acc.index and acc.access usually map an iteration space
 * to a (partial) data space.
 * If the access has arguments, however, then the domain of the
 * mapping is a wrapped mapping from the iteration space
 * to a space of dimensionality equal to the number of arguments.
 * Each dimension in this space corresponds to the value of the
 * corresponding argument.
 *
 * The ranges of the index expressions and access relations may
 * also be wrapped relations, in which case the expression represents
 * a member access, with the structure represented by the domain
 * of this wrapped relation and the member represented by the range.
 * In case of nested member accesses, the domain is itself a wrapped
 * relation.
 *
 * If the data space is unnamed (and 1D), then it represents
 * the set of integers.  That is, the access represents a value that
 * is equal to the index.
 *
 * A double is represented as both an (approximate) value "val" and
 * a string representation "s".
 */
struct pet_expr {
	enum pet_expr_type type;

	unsigned n_arg;
	struct pet_expr **args;

	union {
		struct {
			isl_id *ref_id;
			isl_map *access;
			isl_multi_pw_aff *index;
			int read;
			int write;
		} acc;
		enum pet_op_type op;
		char *name;
		char *type_name;
		struct {
			double val;
			char *s;
		} d;
	};
};

/* Return the potential read access relation of access expression "expr". */
__isl_give isl_map *pet_expr_access_get_may_access(struct pet_expr *expr);
/* Return the tagged potential read access relation of access "expr". */
__isl_give isl_map *pet_expr_access_get_tagged_may_access(
	struct pet_expr *expr);

/* If the statement has arguments, i.e., n_arg != 0, then
 * "domain" is a wrapped map, mapping the iteration domain
 * to the values of the arguments for which this statement
 * is executed.
 * Otherwise, it is simply the iteration domain.
 *
 * If one of the arguments is an access expression that accesses
 * more than one element for a given iteration, then the constraints
 * on the value of this argument (encoded in "domain") should be satisfied
 * for all of those accessed elements.
 */
struct pet_stmt {
	int line;
	isl_set *domain;
	isl_map *schedule;
	struct pet_expr *body;

	unsigned n_arg;
	struct pet_expr **args;
};

/* Construct an associative array from reference identifiers of
 * access expressions in "stmt" to the corresponding isl_ast_expr.
 * Each index expression is first transformed through "fn_index"
 * (if not NULL).  Then an AST expression is generated using "build".
 * Finally, the AST expression is transformed using "fn_expr"
 * (if not NULL).
 */
__isl_give isl_id_to_ast_expr *pet_stmt_build_ast_exprs(struct pet_stmt *stmt,
	__isl_keep isl_ast_build *build,
	__isl_give isl_multi_pw_aff *(*fn_index)(
		__isl_take isl_multi_pw_aff *mpa, __isl_keep isl_id *id,
		void *user), void *user_index,
	__isl_give isl_ast_expr *(*fn_expr)(__isl_take isl_ast_expr *expr,
		__isl_keep isl_id *id, void *user), void *user_expr);

/* Print "stmt" to "p".
 *
 * The access expressions in "stmt" are replaced by the isl_ast_expr
 * associated to its reference identifier in "ref2expr".
 */
__isl_give isl_printer *pet_stmt_print_body(struct pet_stmt *stmt,
	__isl_take isl_printer *p, __isl_keep isl_id_to_ast_expr *ref2expr);

/* This structure represents a defined type.
 * "name" is the name of the type, while "definition" is a string
 * representation of its definition.
 */
struct pet_type {
	char *name;
	char *definition;
};

/* context holds constraints on the parameter that ensure that
 * this array has a valid (i.e., non-negative) size
 *
 * extent holds constraints on the indices
 * 
 * value_bounds holds constraints on the elements of the array
 * and may be NULL if no such constraints were specified by the user
 *
 * element_size is the size in bytes of each array element
 * element_type is the type of the array elements.
 * element_is_record is set if this type is a record type.
 *
 * live_out is set if the array appears in a live-out pragma
 *
 * if uniquely_defined is set then the array is written by a single access
 * such that any element that is ever read
 * is known to be assigned exactly once before the read
 *
 * declared is set if the array was declared somewhere inside the scop.
 * exposed is set if the declared array is visible outside the scop.
 */
struct pet_array {
	isl_set *context;
	isl_set *extent;
	isl_set *value_bounds;
	char *element_type;
	int element_is_record;
	int element_size;
	int live_out;
	int uniquely_defined;
	int declared;
	int exposed;
};

/* This structure represents an implication on a boolean filter.
 * In particular, if the filter value of an element in the domain
 * of "extension" is equal to "satisfied", then the filter values
 * of the corresponding images in "extension" are also equal
 * to "satisfied".
 */
struct pet_implication {
	int satisfied;
	isl_map *extension;
};

/* The start and end fields contain the offsets in the input file
 * of the scop, where end points to the first character after the scop.
 * If the scop was detected based on scop and endscop pragmas, then
 * the lines containing these pragmas are included in this range.
 * Internally, end may be zero to indicate that no offset information is
 * available (yet).
 * The context describes the set of parameter values for which
 * the scop can be executed.
 * context_value describes assignments to the parameters (if any)
 * outside of the scop.
 *
 * The n_type types define types that may be referenced from by the arrays.
 *
 * The n_implication implications describe implications on boolean filters.
 */
struct pet_scop {
	unsigned start;
	unsigned end;

	isl_set *context;
	isl_set *context_value;

	int n_type;
	struct pet_type **types;

	int n_array;
	struct pet_array **arrays;

	int n_stmt;
	struct pet_stmt **stmts;

	int n_implication;
	struct pet_implication **implications;
};

/* Return a textual representation of the operator. */
const char *pet_op_str(enum pet_op_type op);
int pet_op_is_inc_dec(enum pet_op_type op);

/* Extract a pet_scop from a C source file.
 * If function is not NULL, then the pet_scop is extracted from
 * a function with that name.
 */
struct pet_scop *pet_scop_extract_from_C_source(isl_ctx *ctx,
	const char *filename, const char *function);

/* Transform the C source file "input" by rewriting each scop
 * When autodetecting scops, at most one scop per function is rewritten.
 * The transformed C code is written to "output".
 */
int pet_transform_C_source(isl_ctx *ctx, const char *input, FILE *output,
	__isl_give isl_printer *(*transform)(__isl_take isl_printer *p,
		struct pet_scop *scop, void *user), void *user);
/* Given a scop and a printer passed to a pet_transform_C_source callback,
 * print the original corresponding code to the printer.
 */
__isl_give isl_printer *pet_scop_print_original(struct pet_scop *scop,
	__isl_take isl_printer *p);

/* Update all isl_sets and isl_maps such that they all have the same
 * parameters in the same order.
 */
struct pet_scop *pet_scop_align_params(struct pet_scop *scop);

/* Does "scop" contain any data dependent accesses? */
int pet_scop_has_data_dependent_accesses(struct pet_scop *scop);
/* Does "scop" contain any data dependent conditions? */
int pet_scop_has_data_dependent_conditions(struct pet_scop *scop);

void pet_scop_dump(struct pet_scop *scop);
struct pet_scop *pet_scop_free(struct pet_scop *scop);

__isl_give isl_union_set *pet_scop_collect_domains(struct pet_scop *scop);
/* Collect all potential read access relations. */
__isl_give isl_union_map *pet_scop_collect_may_reads(struct pet_scop *scop);
/* Collect all tagged potential read access relations. */
__isl_give isl_union_map *pet_scop_collect_tagged_may_reads(
	struct pet_scop *scop);
/* Collect all potential write access relations. */
__isl_give isl_union_map *pet_scop_collect_may_writes(struct pet_scop *scop);
/* Collect all definite write access relations. */
__isl_give isl_union_map *pet_scop_collect_must_writes(struct pet_scop *scop);
/* Collect all tagged potential write access relations. */
__isl_give isl_union_map *pet_scop_collect_tagged_may_writes(
	struct pet_scop *scop);
/* Collect all tagged definite write access relations. */
__isl_give isl_union_map *pet_scop_collect_tagged_must_writes(
	struct pet_scop *scop);
/* Collect all definite kill access relations. */
__isl_give isl_union_map *pet_scop_collect_must_kills(struct pet_scop *scop);
/* Collect all tagged definite kill access relations. */
__isl_give isl_union_map *pet_scop_collect_tagged_must_kills(
	struct pet_scop *scop);
__isl_give isl_union_map *pet_scop_collect_schedule(struct pet_scop *scop);

#if defined(__cplusplus)
}
#endif

#endif
