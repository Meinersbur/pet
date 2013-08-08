#ifndef PET_CLANG_H
#define PET_CLANG_H

#include <clang/AST/Type.h>

clang::QualType pet_clang_base_type(clang::QualType qt);
clang::RecordDecl *pet_clang_record_decl(clang::QualType T);

#endif
