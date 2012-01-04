if BUNDLED_ISL
    MAYBE_ISL = isl
    ISL_LA = $(top_builddir)/isl/libisl.la -lgmp
endif

SUBDIRS = $(MAYBE_ISL) .
DIST_SUBDIRS = $(MAYBE_ISL)

FORCE:
isl/libisl.la: FORCE
	cd isl; $(MAKE) $(AM_MAKEFLAGS) libisl.la

ACLOCAL_AMFLAGS = -I m4

LIB_ISL = $(ISL_LA) @ISL_LIBS@

lib_LTLIBRARIES = libpet.la
bin_PROGRAMS = pet
noinst_PROGRAMS = pet_scop_cmp
TESTS = pet_test.sh

include_HEADERS = include/pet.h

EXTRA_DIST = \
	tests

INCLUDES = -I$(srcdir) -I$(srcdir)/include

AM_CFLAGS = $(INCLUDES) @ISL_CFLAGS@
AM_CXXFLAGS = $(INCLUDES) $(CLANG_CXXFLAGS) @ISL_CFLAGS@
AM_LDFLAGS = $(CLANG_LDFLAGS)

libpet_la_SOURCES = \
	options.h \
	options.c \
	scan.h \
	scan.cc \
	scop.h \
	scop.c \
	scop_plus.h \
	scop_plus.cc \
	version.h \
	version.c \
	pet.cc
libpet_la_LDFLAGS = -version-info @versioninfo@ $(AM_LDFLAGS)
libpet_la_LIBADD = -lclangFrontend -lclangParse -lclangSema -lclangAnalysis \
	-lclangAST -lclangLex -lclangBasic -lclangDriver -lclangSerialization \
	$(CLANG_LIBS) $(CLANG_LDFLAGS) $(LIB_ISL)

pet_CFLAGS = $(AM_CFLAGS) @LIBYAML_CPPFLAGS@
pet_LDFLAGS = $(AM_LDFLAGS) @LIBYAML_LDFLAGS@
pet_SOURCES = \
	emit.c \
	scop_yaml.h \
	main.c
pet_LDADD = libpet.la \
	-lclangFrontend -lclangParse -lclangSema -lclangAnalysis \
	-lclangAST -lclangLex -lclangBasic -lclangDriver -lclangSerialization \
	$(CLANG_LIBS) $(LIB_ISL) -lyaml

pet_scop_cmp_CFLAGS = $(AM_CFLAGS) @LIBYAML_CPPFLAGS@
pet_scop_cmp_LDFLAGS = @LIBYAML_LDFLAGS@
pet_scop_cmp_LDADD = libpet.la $(LIB_ISL) -lyaml
pet_scop_cmp_SOURCES = \
	scop_yaml.h \
	parse.c \
	pet_scop_cmp.c

dist-hook:
	echo @GIT_HEAD_VERSION@ > $(distdir)/GIT_HEAD_ID

gitversion.h: @GIT_HEAD@
	$(AM_V_GEN)echo '#define GIT_HEAD_ID "'@GIT_HEAD_VERSION@'"' > $@
