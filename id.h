#ifndef PET_ID_H
#define PET_ID_H

#include <clang/AST/Decl.h>
#include <isl/id.h>

__isl_give isl_id *pet_id_from_decl(isl_ctx *ctx, clang::ValueDecl *decl);
__isl_give isl_id *pet_id_from_name_and_decl(isl_ctx *ctx, const char *name,
	clang::ValueDecl *decl);
clang::ValueDecl *pet_id_get_decl(__isl_keep isl_id *id);

#endif
