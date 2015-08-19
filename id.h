#ifndef PET_ID_H
#define PET_ID_H

#include <clang/AST/Decl.h>
#include <isl/id.h>

__isl_give isl_id *pet_id_from_decl(isl_ctx *ctx, clang::ValueDecl *decl);

#endif
