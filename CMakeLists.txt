list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake/modules")
cmake_minimum_required(VERSION 3.2)

project("pet" C CXX)
set(PET_SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR})
set(PET_BINARY_DIR ${CMAKE_CURRENT_BINARY_DIR})

if (NOT TARGET isl)
	message("Searching ISL")
	find_package(Isl REQUIRED)
endif()
message(${ISL_LIBRARIES})

find_package(Clang REQUIRED)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
configure_file(${PET_SOURCE_DIR}/gitversion.h.cmake ${PET_BINARY_DIR}/include/gitversion.h)


configure_file(${PET_SOURCE_DIR}/config.h.cmake ${PET_BINARY_DIR}/include/config.h)



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
target_link_libraries(pet INTERFACE ${ISL_LIBRARIES} ${CLANG_LIBRARIES} "-lyaml")



function(add_pet_executable _name)
  set(_sources ${ARGN})
  add_executable(${_name} ${_sources})
  target_link_libraries(${_name} pet)
endfunction()

add_pet_executable(pet_codegen pet_codegen.c)
add_pet_executable(pet_check_code pet_check_code.c)
add_pet_executable(pet_scop_cmp pet_scop_cmp.c)
