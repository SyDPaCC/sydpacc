dnl autoconf macros for Coq

AC_DEFUN([AC_PROG_COQ],
[dnl
  AC_CHECK_TOOL([COQC],[coqc],[no])

  if test "$COQC" != "no"; then
     COQCVERSION=`$COQC -v | sed -n -e 's|.*version* *\(.*\)|\1|p'`
     AC_MSG_RESULT([Coq version is $COQCVERSION])
  fi

  AC_CHECK_TOOL([COQDEP],[coqdep],[no])
  AC_CHECK_TOOL([COQMAKEFILE],[coq_makefile],[no])
])
