list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
cmake_minimum_required(VERSION 3.2)

project("pet" C CXX)
set(PET_SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}")
set(PET_BINARY_DIR "${CMAKE_CURRENT_BINARY_DIR}")

if (TARGET isl)
	set(ISL_LIBRARIES isl)
else ()
	message("Searching ISL")
	find_package(Isl REQUIRED)
endif()

find_package(Clang REQUIRED)



## Platform introspection
# Determine version of pet
if (EXISTS "${PET_SOURCE_DIR}/GIT_HEAD_ID")
  # The source comes from a 'make dist' archive
  file(READ "${PET_SOURCE_DIR}/GIT_HEAD_ID" GIT_HEAD_ID)
  string(STRIP "${GIT_HEAD_ID}" GIT_HEAD_ID)
elseif (EXISTS "${PET_SOURCE_DIR}/gitversion.h")
  # The source directory is preconfigured
  file(READ "${PET_SOURCE_DIR}/gitversion.h" GITVERSION_H)
  string(REGEX REPLACE ".*\\\"([^\\\"]*)\\\".*" "\\1" GIT_HEAD_ID "${GITVERSION_H}")
elseif (EXISTS "${PET_SOURCE_DIR}/.git" AND "${PET_SOURCE_DIR}" STREQUAL "${CMAKE_CURRENT_SOURCE_DIR}")
  # This is the GIT repository itself
  # GetGitRevisionDescription uses CMAKE_CURRENT_SOURCE_DIR to look for the .git directory, so it must refer to PET's source directory
  include(GetGitRevisionDescription)
  git_describe(GIT_HEAD_ID)
else ()
  # Unknown revision
  set(GIT_HEAD_ID "UNKNOWN")
endif ()
message(STATUS "PET version: ${GIT_HEAD_ID}")


set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
configure_file("${PET_SOURCE_DIR}/gitversion.h.cmake" "${PET_BINARY_DIR}/gitversion.h")
configure_file("${PET_SOURCE_DIR}/config.h.cmake" "${PET_BINARY_DIR}/config.h")

set(libpet_sources
	aff.c
	array.c
	clang.cc
	context.c
	expr.c
	expr_arg.c
	filter.c
	loc.c
	nest.c
	options.c
	parse.c
	print.c
	tree.c
	tree2scop.c
	scan.cc
	scop.c
	scop_plus.cc
	skip.c
	summary.c
	value_bounds.c
	version.cc
	pet.cc
)



add_library(pet ${libpet_sources})
target_include_directories(pet PRIVATE "${PET_BINARY_DIR}/include")
target_include_directories(pet PUBLIC "${PET_SOURCE_DIR}/include")
target_include_directories(pet PRIVATE ${CLANG_INCLUDE_DIRS})
target_link_libraries(pet INTERFACE ${ISL_LIBRARIES} ${CLANG_LIBRARIES} "-lyaml")



function(add_pet_executable _name)
  set(_sources ${ARGN})
  add_executable(${_name} ${_sources})
  target_link_libraries(${_name} pet)
endfunction()

add_pet_executable(pet_codegen pet_codegen.c)
add_pet_executable(pet_check_code pet_check_code.c)
add_pet_executable(pet_scop_cmp pet_scop_cmp.c)
