

if (CLANG_FIND_REQUIRED)
  find_package(LLVM REQUIRED COMPONENTS all)
else()
  find_package(LLVM COMPONENTS all)
endif()




set(CLANG_DEFINITIONS)


set(CLANG_EXECUTABLE "clang")
set(CLANGXX_EXECUTABLE "clang++")


find_path(CLANG_INCLUDE_DIR "clang/Basic/Version.h"
  PATHS ENV CLANG_INCLUDE ENV CLANG_DIR
  NO_DEFAULT_PATH
)
find_path(CLANG_INCLUDE_DIR "clang/Basic/Version.h")
mark_as_advanced(CLANG_INCLUDE_DIR)
set(CLANG_INCLUDE_DIRS "${CLANG_INCLUDE_DIR}")


set(CLANG_LIBRARIES ${LLVM_LIBRARIES} ${LLVM_SYSTEM_LIBS})
mark_as_advanced(CLANG_LIBRARIES)

macro(find_clang_lib _name)
  string(TOUPPER "${_name}" _NAME)
  find_library("CLANG_${_NAME}_LIBRARY" NAMES "clang${_name}"
    HINTS ENV CLANG_LIB ENV CLANG_DIR
    NO_DEFAULT_PATH
  )
  find_library("CLANG_${_NAME}_LIBRARY" NAMES "clang${_name}")
  mark_as_advanced("CLANG_${_NAME}_LIBRARY")
  list(INSERT CLANG_LIBRARIES 0 "${CLANG_${_NAME}_LIBRARY}" )
endmacro()


find_clang_lib(Serialization)
find_clang_lib(Driver)
find_clang_lib(Basic)
find_clang_lib(Lex)
find_clang_lib(AST)
find_clang_lib(Analysis)
find_clang_lib(Edit)
find_clang_lib(Sema)
find_clang_lib(Parse)
find_clang_lib(Frontend)



include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Clang DEFAULT_MSG CLANG_INCLUDE_DIR CLANG_BASIC_LIBRARY)
