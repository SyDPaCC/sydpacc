-include ../../../../config/Makefile.config
OCAMLMAKEFILE = ../../../../Uncertified/Bsml/ocamlmake/OCamlMakefile
CC=$(MPICC)
OCAMLLDFLAGS=-cc $(CC)
LIBDIRS=../../../../Build/Extraction ../../../../Extraction ../../../../Uncertified/Bsml/src ../../../../Build/Uncertified/NatInt 
INCDIRS=../../../../Build/Extraction ../../../../Extraction ../../../../Uncertified/Bsml/src ../../../../Build/Uncertified/NatInt 
LIBS= MapOne bsmlcoq.mpi unix 
CFLAGS= -I$(OCAMLLIBPATH)  -O -g -Wall -fPIC
SOURCES=mapone_run.ml
NO_CUSTOM=true
NCSUFFIX=.native
BCSUFFIX=.byte
RESULT=mapone
-include $(OCAMLMAKEFILE)


