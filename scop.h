#ifndef PET_SCOP_H
#define PET_SCOP_H

#include <pet.h>

#include <isl/aff.h>
#include <isl/id.h>

#if defined(__cplusplus)
extern "C" {
#endif

/* Do we want to skip the rest of the current loop iteration (pet_skip_now)
 * or subsequent loop iterations (pet_skip_later)?
 */
enum pet_skip { pet_skip_now = 0, pet_skip_later = 1 };

const char *pet_type_str(enum pet_expr_type type);
enum pet_expr_type pet_str_type(const char *str);

enum pet_op_type pet_str_op(const char *str);

struct pet_expr *pet_expr_from_index_and_depth(
	__isl_take isl_multi_pw_aff *index, int depth);
struct pet_expr *pet_expr_from_access_and_index(__isl_take isl_map *access,
	__isl_take isl_multi_pw_aff *index);
struct pet_expr *pet_expr_kill_from_access_and_index(__isl_take isl_map *access,
	__isl_take isl_multi_pw_aff *index);
struct pet_expr *pet_expr_new_unary(isl_ctx *ctx, enum pet_op_type op,
	struct pet_expr *arg);
struct pet_expr *pet_expr_new_binary(isl_ctx *ctx, enum pet_op_type op,
	struct pet_expr *lhs, struct pet_expr *rhs);
struct pet_expr *pet_expr_new_ternary(isl_ctx *ctx, struct pet_expr *cond,
	struct pet_expr *lhs, struct pet_expr *rhs);
struct pet_expr *pet_expr_new_call(isl_ctx *ctx, const char *name,
	unsigned n_arg);
struct pet_expr *pet_expr_new_cast(isl_ctx *ctx, const char *type_name,
	struct pet_expr *arg);
struct pet_expr *pet_expr_new_double(isl_ctx *ctx, double d, const char *s);
struct pet_expr *pet_expr_new_int(__isl_take isl_val *v);
void pet_expr_dump(struct pet_expr *expr);

int pet_expr_is_affine(struct pet_expr *expr);
__isl_give isl_id *pet_expr_access_get_id(struct pet_expr *expr);
struct pet_expr *pet_expr_access_align_params(struct pet_expr *expr);
int pet_expr_is_scalar_access(struct pet_expr *expr);
int pet_expr_is_equal(struct pet_expr *expr1, struct pet_expr *expr2);
struct pet_expr *pet_expr_restrict(struct pet_expr *expr,
	__isl_take isl_set *cond);

struct pet_stmt *pet_stmt_from_pet_expr(isl_ctx *ctx, int line,
	__isl_take isl_id *label, int id, struct pet_expr *expr);
void pet_stmt_dump(struct pet_stmt *stmt);
void *pet_stmt_free(struct pet_stmt *stmt);

int pet_stmt_is_assume(struct pet_stmt *stmt);

struct pet_type *pet_type_alloc(isl_ctx *ctx, const char *name,
	const char *definition);
struct pet_type *pet_type_free(struct pet_type *type);

void pet_array_dump(struct pet_array *array);
struct pet_array *pet_array_free(struct pet_array *array);

void *pet_implication_free(struct pet_implication *implication);

struct pet_stmt *pet_stmt_prefix(struct pet_stmt *stmt, int pos);

struct pet_scop *pet_scop_from_pet_stmt(isl_ctx *ctx, struct pet_stmt *stmt);
struct pet_scop *pet_scop_alloc(isl_ctx *ctx);
struct pet_scop *pet_scop_empty(isl_ctx *ctx);
struct pet_scop *pet_scop_add_seq(isl_ctx *ctx, struct pet_scop *scop1,
	struct pet_scop *scop2);
struct pet_scop *pet_scop_add_par(isl_ctx *ctx, struct pet_scop *scop1,
	struct pet_scop *scop2);

int pet_scop_is_equal(struct pet_scop *scop1, struct pet_scop *scop2);

struct pet_scop *pet_scop_prefix(struct pet_scop *scop, int pos);
struct pet_scop *pet_scop_embed(struct pet_scop *scop, __isl_take isl_set *dom,
	__isl_take isl_aff *sched, __isl_take isl_aff *iv_map,
	__isl_take isl_id *id);
struct pet_scop *pet_scop_restrict(struct pet_scop *scop,
	__isl_take isl_set *cond);
struct pet_scop *pet_scop_restrict_context(struct pet_scop *scop,
	__isl_take isl_set *context);
struct pet_scop *pet_scop_reset_context(struct pet_scop *scop);
struct pet_expr *pet_expr_filter(struct pet_expr *expr,
	__isl_take isl_multi_pw_aff *test, int satisfied);
struct pet_scop *pet_scop_filter(struct pet_scop *scop,
	__isl_take isl_multi_pw_aff *test, int satisfied);
struct pet_scop *pet_scop_merge_filters(struct pet_scop *scop);
struct pet_scop *pet_scop_add_implication(struct pet_scop *scop,
	__isl_take isl_map *map, int satisfied);

struct pet_scop *pet_scop_detect_parameter_accesses(struct pet_scop *scop);

struct pet_scop *pet_scop_gist(struct pet_scop *scop,
	__isl_keep isl_union_map *value_bounds);

struct pet_scop *pet_scop_add_ref_ids(struct pet_scop *scop);
struct pet_scop *pet_scop_anonymize(struct pet_scop *scop);

int pet_expr_foreach_access_expr(struct pet_expr *expr,
	int (*fn)(struct pet_expr *expr, void *user), void *user);
struct pet_expr *pet_expr_map_access(struct pet_expr *expr,
	struct pet_expr *(*fn)(struct pet_expr *expr, void *user),
	void *user);

int pet_scop_writes(struct pet_scop *scop, __isl_keep isl_id *id);

int pet_scop_has_skip(struct pet_scop *scop, enum pet_skip type);
int pet_scop_has_affine_skip(struct pet_scop *scop, enum pet_skip type);
int pet_scop_has_universal_skip(struct pet_scop *scop, enum pet_skip type);
int pet_scop_has_var_skip(struct pet_scop *scop, enum pet_skip type);
struct pet_scop *pet_scop_set_skip(struct pet_scop *scop,
	enum pet_skip type, __isl_take isl_multi_pw_aff *skip);
__isl_give isl_multi_pw_aff *pet_scop_get_skip(struct pet_scop *scop,
	enum pet_skip type);
__isl_give isl_set *pet_scop_get_affine_skip_domain(struct pet_scop *scop,
	enum pet_skip type);
__isl_give isl_id *pet_scop_get_skip_id(struct pet_scop *scop,
	enum pet_skip type);
struct pet_expr *pet_scop_get_skip_expr(struct pet_scop *scop,
	enum pet_skip type);
void pet_scop_reset_skip(struct pet_scop *scop, enum pet_skip type);

struct pet_scop *pet_scop_add_array(struct pet_scop *scop,
	struct pet_array *array);

struct pet_scop *pet_scop_update_start_end(struct pet_scop *scop,
	unsigned start, unsigned end);
struct pet_scop *pet_scop_set_input_file(struct pet_scop *scop, FILE *input);

#if defined(__cplusplus)
}
#endif

#endif
