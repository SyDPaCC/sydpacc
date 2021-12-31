-include ../../../config/Makefile.config
OCAMLMAKEFILE = ../../Bsml/ocamlmake/OCamlMakefile
CC=$(MPICC)
OCAMLLDFLAGS=-cc $(CC)
LIBDIRS=../../../Build/Extraction ../../Bsml/src 
INCDIRS=../../../Build/Extraction ../../Bsml/src
LIBS= BsmlBm bsmlcoq.mpi unix
CFLAGS= -I$(OCAMLLIBPATH)  -O -g -Wall -fPIC
SOURCES= character.ml generator.ml bm_run.ml
NO_CUSTOM=true
NCSUFFIX=.native
BCSUFFIX=.byte
RESULT= bm
-include $(OCAMLMAKEFILE)
