#ifndef PET_SCOP_H
#define PET_SCOP_H

#include <pet.h>

#include <isl/id.h>

#if defined(__cplusplus)
extern "C" {
#endif

const char *pet_type_str(enum pet_expr_type type);
enum pet_expr_type pet_str_type(const char *str);

enum pet_op_type pet_str_op(const char *str);

struct pet_expr *pet_expr_from_access(__isl_take isl_map *access);
struct pet_expr *pet_expr_new_unary(isl_ctx *ctx, enum pet_op_type op,
	struct pet_expr *arg);
struct pet_expr *pet_expr_new_binary(isl_ctx *ctx, enum pet_op_type op,
	struct pet_expr *lhs, struct pet_expr *rhs);
struct pet_expr *pet_expr_new_ternary(isl_ctx *ctx, struct pet_expr *cond,
	struct pet_expr *lhs, struct pet_expr *rhs);
struct pet_expr *pet_expr_new_call(isl_ctx *ctx, const char *name,
	unsigned n_arg);
struct pet_expr *pet_expr_new_double(isl_ctx *ctx, double d);
void pet_expr_dump(struct pet_expr *expr);
void *pet_expr_free(struct pet_expr *expr);

int pet_expr_is_equal(struct pet_expr *expr1, struct pet_expr *expr2);
struct pet_expr *pet_expr_restrict(struct pet_expr *expr,
	__isl_take isl_set *cond);

struct pet_stmt *pet_stmt_from_pet_expr(isl_ctx *ctx, int line,
	__isl_take isl_id *label, int id, struct pet_expr *expr);
void pet_stmt_dump(struct pet_stmt *stmt);
void *pet_stmt_free(struct pet_stmt *stmt);

void pet_array_dump(struct pet_array *array);
void *pet_array_free(struct pet_array *array);

struct pet_stmt *pet_stmt_prefix(struct pet_stmt *stmt, int pos);

struct pet_scop *pet_scop_from_pet_stmt(isl_ctx *ctx, struct pet_stmt *stmt);
struct pet_scop *pet_scop_empty(isl_ctx *ctx);
struct pet_scop *pet_scop_add(isl_ctx *ctx, struct pet_scop *scop1,
	struct pet_scop *scop2);

int pet_scop_is_equal(struct pet_scop *scop1, struct pet_scop *scop2);

struct pet_scop *pet_scop_prefix(struct pet_scop *scop, int pos);
struct pet_scop *pet_scop_embed(struct pet_scop *scop, __isl_take isl_set *dom,
	__isl_take isl_map *sched, __isl_take isl_id *id);
struct pet_scop *pet_scop_restrict(struct pet_scop *scop,
	__isl_take isl_set *cond);
struct pet_scop *pet_scop_filter(struct pet_scop *scop,
	__isl_take isl_map *test, int satisfied);

struct pet_scop *pet_scop_detect_parameter_accesses(struct pet_scop *scop);

struct pet_scop *pet_scop_anonymize(struct pet_scop *scop);

struct pet_expr *pet_expr_foreach_access(struct pet_expr *expr,
	__isl_give isl_map *(*fn)(__isl_take isl_map *access, void *user),
	void *user);

int pet_scop_writes(struct pet_scop *scop, __isl_keep isl_id *id);

#if defined(__cplusplus)
}
#endif

#endif
