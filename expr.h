#ifndef PET_EXPR_H
#define PET_EXPR_H

#include <pet.h>

#if defined(__cplusplus)
extern "C" {
#endif

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
int pet_expr_is_scalar_access(struct pet_expr *expr);
int pet_expr_is_equal(struct pet_expr *expr1, struct pet_expr *expr2);

__isl_give isl_id *pet_expr_access_get_id(struct pet_expr *expr);

int pet_expr_foreach_access_expr(struct pet_expr *expr,
	int (*fn)(struct pet_expr *expr, void *user), void *user);
struct pet_expr *pet_expr_map_access(struct pet_expr *expr,
	struct pet_expr *(*fn)(struct pet_expr *expr, void *user),
	void *user);

int pet_expr_writes(struct pet_expr *expr, __isl_keep isl_id *id);

struct pet_expr *pet_expr_access_align_params(struct pet_expr *expr);
struct pet_expr *pet_expr_restrict(struct pet_expr *expr,
	__isl_take isl_set *cond);
struct pet_expr *pet_expr_access_update_domain(struct pet_expr *expr,
	__isl_keep isl_multi_pw_aff *update);
struct pet_expr *pet_expr_update_domain(struct pet_expr *expr,
	__isl_take isl_multi_pw_aff *update);
struct pet_expr *pet_expr_align_params(struct pet_expr *expr,
	__isl_take isl_space *space);
struct pet_expr *pet_expr_filter(struct pet_expr *expr,
	__isl_take isl_multi_pw_aff *test, int satisfied);
struct pet_expr *pet_expr_detect_parameter_accesses(struct pet_expr *expr,
	__isl_take isl_space *space);
struct pet_expr *pet_expr_add_ref_ids(struct pet_expr *expr, int *n_ref);
struct pet_expr *pet_expr_anonymize(struct pet_expr *expr);
struct pet_expr *pet_expr_gist(struct pet_expr *expr,
	__isl_keep isl_set *context, __isl_keep isl_union_map *value_bounds);

__isl_give isl_map *pet_expr_tag_access(struct pet_expr *expr,
	__isl_take isl_map *access);

void pet_expr_dump_with_indent(struct pet_expr *expr, int indent);

#if defined(__cplusplus)
}
#endif

#endif
