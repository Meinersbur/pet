#ifndef PET_H
#define PET_H

#include <isl/arg.h>
#include <isl/set.h>
#include <isl/map.h>
#include <isl/union_map.h>

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
 * op is valid otherwise
 *
 * acc.access usually maps an iteration space to a data space.
 * If the access has arguments, however, then the domain of the
 * mapping is a wrapped mapping from the iteration space
 * to a space of dimensionality equal to the number of arguments.
 * Each dimension in this space corresponds to the value of the
 * corresponding argument.
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
			isl_map *access;
			int read;
			int write;
		} acc;
		enum pet_op_type op;
		char *name;
		struct {
			double val;
			char *s;
		} d;
	};
};

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

/* context holds constraints on the parameter that ensure that
 * this array has a valid (i.e., non-negative) size
 *
 * extent holds constraints on the indices
 * 
 * value_bounds holds constraints on the elements of the array
 * and may be NULL if no such constraints were specified by the user
 *
 * element_size is the size in bytes of each array element
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
	int element_size;
	int live_out;
	int uniquely_defined;
	int declared;
	int exposed;
};

/* The context describes the set of parameter values for which
 * the scop can be executed.
 * context_value describes assignments to the parameters (if any)
 * outside of the scop.
 */
struct pet_scop {
	isl_set *context;
	isl_set *context_value;

	int n_array;
	struct pet_array **arrays;

	int n_stmt;
	struct pet_stmt **stmts;
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

/* Update all isl_sets and isl_maps such that they all have the same
 * parameters in the same order.
 */
struct pet_scop *pet_scop_align_params(struct pet_scop *scop);

void pet_scop_dump(struct pet_scop *scop);
void *pet_scop_free(struct pet_scop *scop);

__isl_give isl_union_set *pet_scop_collect_domains(struct pet_scop *scop);
/* Collect all read access relations. */
__isl_give isl_union_map *pet_scop_collect_reads(struct pet_scop *scop);
/* Collect all write access relations. */
__isl_give isl_union_map *pet_scop_collect_writes(struct pet_scop *scop);
__isl_give isl_union_map *pet_scop_collect_schedule(struct pet_scop *scop);

#if defined(__cplusplus)
}
#endif

#endif
