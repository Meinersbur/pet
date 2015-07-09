
find_package(Gmp REQUIRED)

set(ISL_DEFINITIONS)

find_path(ISL_INCLUDE_DIR isl/ctx.h
  PATHS ENV ISL_INCLUDE ENV ISL_DIR 
  NO_DEFAULT_PATH
)
find_path(ISL_INCLUDE_DIR isl/ctx.h)
mark_as_advanced(ISL_INCLUDE_DIR)
set(ISL_INCLUDE_DIRS ${ISL_INCLUDE_DIR})

find_library(ISL_LIBRARY NAMES isl
  HINTS ENV ISL_LIB ENV ISL_DIR
  NO_DEFAULT_PATH
)
find_library(ISL_LIBRARY NAMES isl)
mark_as_advanced(ISL_LIBRARY)
set(ISL_LIBRARIES ${ISL_LIBRARY} ${GMP_LIBRARY})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Isl DEFAULT_MSG ISL_LIBRARY ISL_INCLUDE_DIR)
