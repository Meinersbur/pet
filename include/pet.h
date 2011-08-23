#ifndef PET_H
#define PET_H

#include <isl/set.h>
#include <isl/map.h>
#include <isl/union_map.h>

#if defined(__cplusplus)
extern "C" {
#endif

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
	pet_op_eq,
	pet_op_le,
	pet_op_lt,
	pet_op_gt,
	pet_op_minus,
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
 * call is valid when type == pet_expr_call
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
		double d;
	};
};

struct pet_stmt {
	int line;
	isl_set *domain;
	isl_map *schedule;
	struct pet_expr *body;
};

/* context holds constraints on the parameter that ensure that
 * this array has a valid (i.e., non-negative) size
 *
 * extent holds constraints on the indices
 * 
 * value_bounds holds constraints on the elements of the array
 * and may be NULL if no such constraints were specified by the user
 *
 * live_out is set if the array appears in a live-out pragma
 */
struct pet_array {
	isl_set *context;
	isl_set *extent;
	isl_set *value_bounds;
	char *element_type;
	int live_out;
};

struct pet_scop {
	isl_set *context;

	int n_array;
	struct pet_array **arrays;

	int n_stmt;
	struct pet_stmt **stmts;
};

/* Return a textual representation of the operator. */
const char *pet_op_str(enum pet_op_type op);

/* Extract a pet_scop from a C source file.
 * If function is not NULL, then the pet_scop is extracted from
 * a function with that name.
 *
 * If autodetect is set, any valid scop is extracted.
 * Otherwise, the scop needs to be delimited by pragmas.
 */
struct pet_scop *pet_scop_extract_from_C_source(isl_ctx *ctx,
	const char *filename, const char *function, int autodetect);

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
