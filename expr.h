#ifndef PET_EXPR_H
#define PET_EXPR_H

#include <isl/id_to_pw_aff.h>

#include <pet.h>

#include "context.h"

#if defined(__cplusplus)
extern "C" {
#endif

/* d is valid when type == pet_expr_double
 * i isl valid when type == pet_expr_int
 * acc is valid when type == pet_expr_access
 * name is valid when type == pet_expr_call
 * type is valid when type == pet_expr_cast
 * op is valid otherwise
 *
 * If type_size is not zero, then the expression is of an integer type
 * and type_size represents the size of the type in bits.
 * If type_size is greater than zero, then the type is unsigned
 * and the number of bits is equal to type_size.
 * If type_size is less than zero, then the type is signed
 * and the number of bits is equal to -type_size.
 * type_size may also be zero if the size is (still) unknown.
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
	int ref;
	isl_ctx *ctx;

	enum pet_expr_type type;

	int type_size;

	unsigned n_arg;
	pet_expr **args;

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
		isl_val *i;
	};
};

const char *pet_type_str(enum pet_expr_type type);
enum pet_expr_type pet_str_type(const char *str);

enum pet_op_type pet_str_op(const char *str);

__isl_give pet_expr *pet_expr_alloc(isl_ctx *ctx, enum pet_expr_type type);
__isl_give pet_expr *pet_expr_from_index_and_depth(int type_size,
	__isl_take isl_multi_pw_aff *index, int depth);
__isl_give pet_expr *pet_expr_from_access_and_index(__isl_take isl_map *access,
	__isl_take isl_multi_pw_aff *index);
__isl_give pet_expr *pet_expr_kill_from_access_and_index(
	__isl_take isl_map *access, __isl_take isl_multi_pw_aff *index);
__isl_give pet_expr *pet_expr_new_unary(enum pet_op_type op,
	__isl_take pet_expr *arg);
__isl_give pet_expr *pet_expr_new_binary(int type_size, enum pet_op_type op,
	__isl_take pet_expr *lhs, __isl_take pet_expr *rhs);
__isl_give pet_expr *pet_expr_new_ternary(__isl_take pet_expr *cond,
	__isl_take pet_expr *lhs, __isl_take pet_expr *rhs);
__isl_give pet_expr *pet_expr_new_call(isl_ctx *ctx, const char *name,
	unsigned n_arg);
__isl_give pet_expr *pet_expr_new_cast(const char *type_name,
	__isl_take pet_expr *arg);
__isl_give pet_expr *pet_expr_new_double(isl_ctx *ctx, double d, const char *s);
__isl_give pet_expr *pet_expr_new_int(__isl_take isl_val *v);

__isl_give pet_expr *pet_expr_cow(__isl_take pet_expr *expr);

__isl_give isl_pw_aff *pet_expr_extract_affine(__isl_keep pet_expr *expr,
	__isl_keep pet_context *pc);
__isl_give isl_pw_aff *pet_expr_extract_affine_condition(
	__isl_keep pet_expr *expr, __isl_keep pet_context *pc);
__isl_give isl_pw_aff *pet_expr_extract_comparison(enum pet_op_type op,
	__isl_keep pet_expr *lhs, __isl_keep pet_expr *rhs,
	__isl_keep pet_context *pc);

int pet_expr_is_boolean(__isl_keep pet_expr *expr);
int pet_expr_is_comparison(__isl_keep pet_expr *expr);
int pet_expr_is_min(__isl_keep pet_expr *expr);
int pet_expr_is_max(__isl_keep pet_expr *expr);
int pet_expr_is_scalar_access(__isl_keep pet_expr *expr);
int pet_expr_is_equal(__isl_keep pet_expr *expr1, __isl_keep pet_expr *expr2);

__isl_give isl_space *pet_expr_access_get_parameter_space(
	__isl_take pet_expr *expr);
__isl_give isl_space *pet_expr_access_get_data_space(__isl_keep pet_expr *expr);

__isl_give pet_expr *pet_expr_map_access(__isl_take pet_expr *expr,
	__isl_give pet_expr *(*fn)(__isl_take pet_expr *expr, void *user),
	void *user);

__isl_give isl_map *pet_expr_access_get_access(__isl_keep pet_expr *expr);
__isl_give pet_expr *pet_expr_access_set_access(__isl_take pet_expr *expr,
	__isl_take isl_map *access);
__isl_give pet_expr *pet_expr_access_set_index(__isl_take pet_expr *expr,
	__isl_take isl_multi_pw_aff *index);

int pet_expr_writes(__isl_keep pet_expr *expr, __isl_keep isl_id *id);

__isl_give pet_expr *pet_expr_access_move_dims(__isl_take pet_expr *expr,
	enum isl_dim_type dst_type, unsigned dst_pos,
	enum isl_dim_type src_type, unsigned src_pos, unsigned n);
__isl_give pet_expr *pet_expr_access_pullback_multi_aff(
	__isl_take pet_expr *expr, __isl_take isl_multi_aff *ma);
__isl_give pet_expr *pet_expr_access_pullback_multi_pw_aff(
	__isl_take pet_expr *expr, __isl_take isl_multi_pw_aff *mpa);
__isl_give pet_expr *pet_expr_access_align_params(__isl_take pet_expr *expr);
__isl_give pet_expr *pet_expr_restrict(__isl_take pet_expr *expr,
	__isl_take isl_set *cond);
__isl_give pet_expr *pet_expr_access_update_domain(__isl_take pet_expr *expr,
	__isl_keep isl_multi_pw_aff *update);
__isl_give pet_expr *pet_expr_update_domain(__isl_take pet_expr *expr,
	__isl_take isl_multi_pw_aff *update);
__isl_give pet_expr *pet_expr_align_params(__isl_take pet_expr *expr,
	__isl_take isl_space *space);
__isl_give pet_expr *pet_expr_filter(__isl_take pet_expr *expr,
	__isl_take isl_multi_pw_aff *test, int satisfied);
__isl_give pet_expr *pet_expr_detect_parameter_accesses(
	__isl_take pet_expr *expr, __isl_take isl_space *space);
__isl_give pet_expr *pet_expr_add_ref_ids(__isl_take pet_expr *expr,
	int *n_ref);
__isl_give pet_expr *pet_expr_anonymize(__isl_take pet_expr *expr);
__isl_give pet_expr *pet_expr_gist(__isl_take pet_expr *expr,
	__isl_keep isl_set *context, __isl_keep isl_union_map *value_bounds);

__isl_give isl_map *pet_expr_tag_access(__isl_keep pet_expr *expr,
	__isl_take isl_map *access);

int pet_expr_get_type_size(__isl_keep pet_expr *expr);
__isl_give pet_expr *pet_expr_set_type_size(__isl_take pet_expr *expr,
	int type_size);

void pet_expr_dump_with_indent(__isl_keep pet_expr *expr, int indent);

#if defined(__cplusplus)
}
#endif

#endif
