-include ../../../config/Makefile.config
OCAMLMAKEFILE = ../../Bsml/ocamlmake/OCamlMakefile
CC=$(MPICC)
OCAMLLDFLAGS=-cc $(CC)
LIBDIRS=../../../Build/Extraction ../../Bsml/src 
INCDIRS=../../../Build/Extraction ../../Bsml/src
LIBS= BsmlMps bsmlcoq.mpi
CFLAGS= -I$(OCAMLLIBPATH)  -O -g -Wall -fPIC
SOURCES= numint.ml mps_run.ml
NO_CUSTOM=true
NCSUFFIX=.native
BCSUFFIX=.byte
RESULT= mps
-include $(OCAMLMAKEFILE)
