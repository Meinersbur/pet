#ifndef PET_AFF_H
#define PET_AFF_H

#include <pet.h>

#include <isl/aff.h>

#if defined(__cplusplus)
extern "C" {
#endif

__isl_give isl_pw_aff *pet_and(__isl_take isl_pw_aff *lhs,
	__isl_take isl_pw_aff *rhs);
__isl_give isl_pw_aff *pet_not(__isl_take isl_pw_aff *pa);
__isl_give isl_pw_aff *pet_to_bool(__isl_take isl_pw_aff *pa);
__isl_give isl_pw_aff *pet_boolean(enum pet_op_type type,
	__isl_take isl_pw_aff *pa1, __isl_take isl_pw_aff *pa2);
__isl_give isl_pw_aff *pet_comparison(enum pet_op_type type,
	__isl_take isl_pw_aff *pa1, __isl_take isl_pw_aff *pa2);

#if defined(__cplusplus)
}
#endif

#endif
