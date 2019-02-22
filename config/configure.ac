AC_INIT(SyDPaCC,0.2)
AC_COPYRIGHT(Copyright 2015 Universite d'Orleans & Inria)

AC_CONFIG_MACRO_DIR([m4])

AC_PROG_COQ
if test "$COQC" = "no"; then
   AC_MSG_ERROR([You must install the Coq proof assistant])
fi

AC_PROG_OCAML
if test "$OCAMLC" = "no"; then
   AC_MSG_ERROR([You must install the OCaml compiler])
fi

AC_PROG_CC([mpicc gcc cc])

AX_MPI(
  HAVE_MPI="yes",
  AC_MSG_ERROR([You must install an MPI library])
)

AC_CONFIG_FILES(
  Makefile.config
)
AC_OUTPUT

if test "$prefix" = "NONE"; then
  prefix=$ac_default_prefix
fi

bindir="`eval echo ${bindir}`"
bindir="`eval echo ${bindir}`"

echo
echo Executables will be installed in ${bindir}
