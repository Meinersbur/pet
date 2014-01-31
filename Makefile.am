if BUNDLED_ISL
    MAYBE_ISL = isl
    ISL_LA = $(top_builddir)/isl/libisl.la
endif

SUBDIRS = $(MAYBE_ISL) .
DIST_SUBDIRS = $(MAYBE_ISL)

FORCE:
isl/libisl.la: FORCE
	cd isl; $(MAKE) $(AM_MAKEFLAGS) libisl.la

ACLOCAL_AMFLAGS = -I m4

LIB_ISL = $(ISL_LA) @ISL_LIBS@

lib_LTLIBRARIES = libpet.la
bin_PROGRAMS = @extra_bin_programs@
noinst_PROGRAMS = @extra_noinst_programs@ pet_codegen pet_check_code
EXTRA_PROGRAMS = pet pet_scop_cmp
TESTS = @extra_tests@
EXTRA_TESTS = pet_test.sh codegen_test.sh
TEST_EXTENSIONS = .sh

include_HEADERS = include/pet.h

EXTRA_DIST = \
	tests

PET_INCLUDES = -I$(srcdir) -I$(srcdir)/include

AM_CFLAGS = $(PET_INCLUDES) @ISL_CFLAGS@
AM_CXXFLAGS = $(PET_INCLUDES) $(CLANG_CXXFLAGS) @ISL_CFLAGS@
AM_LDFLAGS = $(CLANG_LDFLAGS)

libpet_la_SOURCES = \
	clang.h \
	clang.cc \
	expr.h \
	expr.c \
	filter.h \
	filter.c \
	options.h \
	options.c \
	print.c \
	print.h \
	scan.h \
	scan.cc \
	scop.h \
	scop.c \
	scop_plus.h \
	scop_plus.cc \
	value_bounds.h \
	value_bounds.c \
	version.h \
	version.cc \
	pet.cc
libpet_la_LDFLAGS = -version-info @versioninfo@ $(AM_LDFLAGS)
libpet_la_LIBADD = -lclangFrontend -lclangParse -lclangSema \
	$(LIB_CLANG_EDIT) -lclangAnalysis \
	-lclangAST -lclangLex -lclangBasic -lclangDriver -lclangSerialization \
	$(CLANG_LIBS) $(CLANG_LDFLAGS) $(LIB_ISL)

pet_CFLAGS = $(AM_CFLAGS) @LIBYAML_CPPFLAGS@
pet_LDFLAGS = $(AM_LDFLAGS) @LIBYAML_LDFLAGS@
pet_SOURCES = \
	dummy.cc \
	emit.c \
	scop_yaml.h \
	main.c
pet_LDADD = libpet.la $(LIB_ISL) -lyaml

pet_scop_cmp_CFLAGS = $(AM_CFLAGS) @LIBYAML_CPPFLAGS@
pet_scop_cmp_LDFLAGS = @LIBYAML_LDFLAGS@
pet_scop_cmp_LDADD = libpet.la $(LIB_ISL) -lyaml
pet_scop_cmp_SOURCES = \
	scop_yaml.h \
	parse.c \
	pet_scop_cmp.c

pet_codegen_CFLAGS = $(AM_CFLAGS)
pet_codegen_LDFLAGS =
pet_codegen_LDADD = libpet.la $(LIB_ISL)
pet_codegen_SOURCES = \
	pet_codegen.c

pet_check_code_CFLAGS = $(AM_CFLAGS)
pet_check_code_LDFLAGS =
pet_check_code_LDADD = libpet.la $(LIB_ISL)
pet_check_code_SOURCES = \
	dummy.cc \
	pet_check_code.c

dist-hook:
	echo @GIT_HEAD_VERSION@ > $(distdir)/GIT_HEAD_ID

gitversion.h: @GIT_HEAD@
	$(AM_V_GEN)echo '#define GIT_HEAD_ID "'@GIT_HEAD_VERSION@'"' > $@
