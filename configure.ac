AC_INIT([pet], [0.02], [isl-development@googlegroups.com])
AC_CONFIG_AUX_DIR([build-aux])
AC_CONFIG_MACRO_DIR([m4])
AM_INIT_AUTOMAKE([foreign])
m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([yes])])
AC_SUBST(versioninfo)
versioninfo=2:0:0

AC_PROG_CC
AC_PROG_CXX
AC_PROG_LIBTOOL

AC_SUBST(CLANG_CXXFLAGS)
AC_SUBST(CLANG_LDFLAGS)
AC_SUBST(CLANG_LIBS)
AX_SUBMODULE(clang,system,system)
llvm_config="llvm-config"
AC_CHECK_PROG([llvm_config_found], ["$llvm_config"], [yes])
if test "x$with_clang_prefix" != "x"; then
	llvm_config="$with_clang_prefix/bin/llvm-config"
	if test -x "$llvm_config"; then
		llvm_config_found=yes
	fi
fi
if test "$llvm_config_found" != yes; then
	AC_MSG_ERROR([llvm-config not found])
fi
CLANG_CXXFLAGS=`$llvm_config --cxxflags`
CLANG_LDFLAGS=`$llvm_config --ldflags`
targets=`$llvm_config --targets-built`
CLANG_LIBS=`$llvm_config --libs $targets asmparser support mc`
CLANG_PREFIX=`$llvm_config --prefix`
AC_DEFINE_UNQUOTED(CLANG_PREFIX, ["$CLANG_PREFIX"], [Clang installation prefix])

SAVE_CPPFLAGS="$CPPFLAGS"
CPPFLAGS="$CLANG_CXXFLAGS $CPPFLAGS"
AC_LANG_PUSH(C++)
AC_CHECK_HEADER([clang/Basic/SourceLocation.h], [],
	[AC_ERROR([clang header file not found])])
AC_EGREP_HEADER([getDefaultTargetTriple], [llvm/Support/Host.h], [],
	[AC_DEFINE([getDefaultTargetTriple], [getHostTriple],
	[Define to getHostTriple for older versions of clang])])
AC_EGREP_HEADER([getExpansionLineNumber], [clang/Basic/SourceLocation.h], [],
	[AC_DEFINE([getExpansionLineNumber], [getInstantiationLineNumber],
	[Define to getInstantiationLineNumber for older versions of clang])])
AC_EGREP_HEADER([getExpansionLoc], [clang/Basic/SourceManager.h], [],
	[AC_DEFINE([getExpansionLoc], [getInstantiationLoc],
	[Define to getInstantiationLoc for older versions of clang])])
AC_EGREP_HEADER([DiagnosticConsumer], [clang/Basic/Diagnostic.h], [],
	[AC_DEFINE([DiagnosticConsumer], [DiagnosticClient],
	[Define to DiagnosticClient for older versions of clang])])
AC_EGREP_HEADER([DiagnosticsEngine], [clang/Basic/Diagnostic.h],
	[AC_DEFINE([DiagnosticInfo], [Diagnostic],
	[Define to Diagnostic for newer versions of clang])],
	[AC_DEFINE([DiagnosticsEngine], [Diagnostic],
	[Define to Diagnostic for older versions of clang])])
AC_EGREP_HEADER([ArrayRef], [clang/Driver/Driver.h],
	[AC_DEFINE([USE_ARRAYREF], [],
		[Define if Driver::BuildCompilation takes ArrayRef])])
AC_EGREP_HEADER([CXXIsProduction], [clang/Driver/Driver.h],
	[AC_DEFINE([HAVE_CXXISPRODUCTION], [],
		[Define if Driver constructor takes CXXIsProduction argument])])
AC_EGREP_HEADER([void HandleTopLevelDecl\(], [clang/AST/ASTConsumer.h],
	[AC_DEFINE([HandleTopLevelDeclReturn], [void],
		   [Return type of HandleTopLevelDeclReturn])
	 AC_DEFINE([HandleTopLevelDeclContinue], [],
		   [Return type of HandleTopLevelDeclReturn])],
	[AC_DEFINE([HandleTopLevelDeclReturn], [bool],
		   [Return type of HandleTopLevelDeclReturn])
	 AC_DEFINE([HandleTopLevelDeclContinue], [true],
		   [Return type of HandleTopLevelDeclReturn])])
AC_EGREP_HEADER([isEnclosingLocal,], [clang/AST/Expr.h],
	[AC_DEFINE([DECLREFEXPR_CREATE_REQUIRES_BOOL], [],
	    [Define if DeclRefExpr::Create takes isEnclosingLocal argument])])
AC_EGREP_HEADER([HasTemplateKWAndArgsInfo], [clang/AST/Expr.h],
	[AC_DEFINE([DECLREFEXPR_CREATE_REQUIRES_SOURCELOCATION], [],
		[Define if DeclRefExpr::Create takes SourceLocation argument])])
AC_CHECK_HEADER([clang/Basic/DiagnosticOptions.h],
	[AC_DEFINE([HAVE_BASIC_DIAGNOSTICOPTIONS_H], [],
		   [Define if clang/Basic/DiagnosticOptions.h exists])])
AC_CHECK_HEADER([clang/Lex/HeaderSearchOptions.h],
	[AC_DEFINE([HAVE_LEX_HEADERSEARCHOPTIONS_H], [],
		   [Define if clang/Lex/HeaderSearchOptions.h exists])], [],
	[#include <clang/Basic/LLVM.h>])
AC_CHECK_HEADER([clang/Lex/PreprocessorOptions.h],
	[AC_DEFINE([HAVE_LEX_PREPROCESSOROPTIONS_H], [],
		   [Define if clang/Lex/PreprocessorOptions.h exists])], [],
	[#include <clang/Basic/LLVM.h>])
AC_LANG_POP
CPPFLAGS="$SAVE_CPPFLAGS"

SAVE_LDFLAGS="$LDFLAGS"
LDFLAGS="$CLANG_LDFLAGS $LDFLAGS"
AC_SUBST(LIB_CLANG_EDIT)
AC_CHECK_LIB([clangEdit], [main], [LIB_CLANG_EDIT=-lclangEdit], [])
LDFLAGS="$SAVE_LDFLAGS"

AX_SUBMODULE(gmp,system|build,system)

AC_SUBST(GMP_LDFLAGS)
AC_SUBST(GMP_LIBS)
case "$with_gmp" in
system)
	if test "x$with_gmp_prefix" != "x"; then
		GMP_CPPFLAGS="-I$with_gmp_prefix/include"
		GMP_LDFLAGS="-L$with_gmp_prefix/lib"
	fi
	GMP_LIBS=-lgmp
	;;
build)
	GMP_CPPFLAGS="-I$gmp_srcdir -I$with_gmp_builddir"
	GMP_LIBS="$with_gmp_builddir/libgmp.la"
	;;
esac

AX_SUBMODULE(isl,build|bundled|system,bundled)
AM_CONDITIONAL(BUNDLED_ISL, test $with_isl = bundled)

AC_SUBST(ISL_CFLAGS)
AC_SUBST(ISL_LIBS)
case "$with_isl" in
bundled)
	ISL_CFLAGS="-I\$(top_srcdir)/isl/include -I\$(top_builddir)/isl/include"
	ISL_CFLAGS="$ISL_CFLAGS $GMP_CPPFLAGS"
	;;
build)
	ISL_BUILDDIR=`echo @abs_builddir@ | $with_isl_builddir/config.status --file=-`
	ISL_CFLAGS="-I$isl_srcdir/include -I$ISL_BUILDDIR/include"
	ISL_CFLAGS="$ISL_CFLAGS $GMP_CPPFLAGS"
	ISL_LIBS="$with_isl_builddir/libisl.la $GMP_LDFLAGS $GMP_LIBS"
	;;
system)
	PKG_CHECK_MODULES([ISL], [isl])
	PACKAGE_CFLAGS_ISL="$ISL_CFLAGS"
esac

AX_SUBMODULE(libyaml,system|no,system)
AC_SUBST(LIBYAML_CPPFLAGS)
AC_SUBST(LIBYAML_LDFLAGS)
if test "x$with_libyaml_prefix" != "x"; then
	LIBYAML_CPPFLAGS="-I$with_libyaml_prefix/include"
fi
if test "x$with_libyaml_exec_prefix" != "x"; then
	LIBYAML_LDFLAGS="-L$with_libyaml_exec_prefix/lib"
fi

if test "$with_libyaml" = "system"; then
	SAVE_CPPFLAGS=$CPPFLAGS
	CPPFLAGS="$CPPFLAGS $LIBYAML_CPPFLAGS"
	AC_CHECK_HEADER([yaml.h],[],[with_libyaml="no"])
	CPPFLAGS="$SAVE_CPPFLAGS"
fi

AC_SUBST(extra_bin_programs)
AC_SUBST(extra_noinst_programs)
AC_SUBST(extra_tests)

if test "$with_libyaml" != "no"; then
	extra_bin_programs="pet"
	extra_noinst_programs="pet_scop_cmp"
	extra_tests="pet_test.sh"
fi

PACKAGE_CFLAGS="$PACKAGE_CFLAGS_ISL"
PACKAGE_LIBS="-lpet -lisl"
AX_CREATE_PKGCONFIG_INFO

AX_DETECT_GIT_HEAD
echo '#define GIT_HEAD_ID "'$GIT_HEAD_ID'"' > gitversion.h

AC_CONFIG_HEADERS(config.h)
AC_CONFIG_FILES(Makefile)
AC_CONFIG_FILES([pet_test.sh], [chmod +x pet_test.sh])
if test $with_isl = bundled; then
	AC_CONFIG_SUBDIRS(isl)
fi
AC_OUTPUT
