AC_INIT([pet], [0.00])
AC_CONFIG_AUX_DIR([build-aux])
AC_CONFIG_MACRO_DIR([m4])
AM_INIT_AUTOMAKE([foreign])
m4_ifdef([AM_SILENT_RULES],[AM_SILENT_RULES([yes])])

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
CLANG_LIBS=`$llvm_config --libs`
CLANG_PREFIX=`$llvm_config --prefix`
AC_DEFINE_UNQUOTED(CLANG_PREFIX, ["$CLANG_PREFIX"], [Clang installation prefix])

SAVE_CPPFLAGS="$CPPFLAGS"
CPPFLAGS="$CLANG_CXXFLAGS $CPPFLAGS"
AC_LANG_PUSH(C++)
AC_CHECK_HEADER([clang/Basic/SourceLocation.h], [],
	[AC_ERROR([clang header file not found])])
AC_EGREP_HEADER([getExpansionLineNumber], [clang/Basic/SourceLocation.h], [],
	[AC_DEFINE([getExpansionLineNumber], [getInstantiationLineNumber],
	[Define to getInstantiationLineNumber for older versions of clang])])
AC_EGREP_HEADER([DiagnosticConsumer], [clang/Basic/Diagnostic.h], [],
	[AC_DEFINE([DiagnosticConsumer], [DiagnosticClient],
	[Define to DiagnosticClient for older versions of clang])])
AC_EGREP_HEADER([DiagnosticsEngine], [clang/Basic/Diagnostic.h],
	[AC_DEFINE([DiagnosticInfo], [Diagnostic],
	[Define to Diagnostic for newer versions of clang])],
	[AC_DEFINE([DiagnosticsEngine], [Diagnostic],
	[Define to Diagnostic for older versions of clang])])
AC_LANG_POP
CPPFLAGS="$SAVE_CPPFLAGS"

AX_SUBMODULE(isl,build|bundled|system,bundled)
AM_CONDITIONAL(BUNDLED_ISL, test $with_isl = bundled)

AC_SUBST(ISL_CFLAGS)
AC_SUBST(ISL_LIBS)
case "$with_isl" in
bundled)
	ISL_CFLAGS="-I\$(top_srcdir)/isl/include -I\$(top_builddir)/isl/include"
	;;
build)
	ISL_BUILDDIR=`echo @abs_builddir@ | $with_isl_builddir/config.status --file=-`
	ISL_CFLAGS="-I$isl_srcdir/include -I$ISL_BUILDDIR/include"
	ISL_LIBS="$with_isl_builddir/libisl.la"
	;;
system)
	PKG_CHECK_MODULES([ISL], [isl])
	PACKAGE_CFLAGS_ISL="$ISL_CFLAGS"
esac

AX_SUBMODULE(libyaml,system,system)
AC_SUBST(LIBYAML_CPPFLAGS)
AC_SUBST(LIBYAML_LDFLAGS)
if test "x$with_libyaml_prefix" != "x"; then
	LIBYAML_CPPFLAGS="-I$with_libyaml_prefix/include"
fi
if test "x$with_libyaml_exec_prefix" != "x"; then
	LIBYAML_LDFLAGS="-L$with_libyaml_exec_prefix/lib"
fi

PACKAGE_CFLAGS="$PACKAGE_CFLAGS_ISL"
PACKAGE_LIBS="-lpet -lisl"
AX_CREATE_PKGCONFIG_INFO

AC_CONFIG_HEADERS(config.h)
AC_CONFIG_FILES(Makefile)
AC_CONFIG_FILES([pet_test.sh], [chmod +x pet_test.sh])
if test $with_isl = bundled; then
	AC_CONFIG_SUBDIRS(isl)
fi
AC_OUTPUT
