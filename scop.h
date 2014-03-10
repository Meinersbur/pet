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

struct pet_stmt *pet_stmt_from_pet_expr(__isl_take isl_set *domain,
	__isl_take pet_loc *loc, __isl_take isl_id *label, int id,
	__isl_take pet_expr *expr);
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

struct pet_scop *pet_scop_intersect_domain_prefix(struct pet_scop *scop,
	__isl_take isl_set *domain);
struct pet_scop *pet_scop_prefix(struct pet_scop *scop, int pos);
struct pet_scop *pet_scop_embed(struct pet_scop *scop, __isl_take isl_set *dom,
	__isl_take isl_aff *sched, __isl_take isl_aff *iv_map,
	__isl_take isl_id *id);
struct pet_scop *pet_scop_restrict(struct pet_scop *scop,
	__isl_take isl_set *cond);
struct pet_scop *pet_scop_restrict_context(struct pet_scop *scop,
	__isl_take isl_set *context);
struct pet_scop *pet_scop_reset_context(struct pet_scop *scop);
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
__isl_give pet_expr *pet_scop_get_skip_expr(struct pet_scop *scop,
	enum pet_skip type);
void pet_scop_reset_skip(struct pet_scop *scop, enum pet_skip type);

struct pet_scop *pet_scop_add_array(struct pet_scop *scop,
	struct pet_array *array);
__isl_give isl_multi_pw_aff *pet_create_test_index(__isl_take isl_space *space,
	int test_nr);
struct pet_scop *pet_scop_add_boolean_array(struct pet_scop *scop,
	__isl_take isl_multi_pw_aff *index, int int_size);

struct pet_scop *pet_scop_update_start_end(struct pet_scop *scop,
	unsigned start, unsigned end);
struct pet_scop *pet_scop_update_start_end_from_loc(struct pet_scop *scop,
	__isl_keep pet_loc *loc);
struct pet_scop *pet_scop_set_loc(struct pet_scop *scop,
	__isl_take pet_loc *loc);
struct pet_scop *pet_scop_set_input_file(struct pet_scop *scop, FILE *input);

#if defined(__cplusplus)
}
#endif

#endif
