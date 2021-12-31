-include ../../../../config/Makefile.config
OCAMLMAKEFILE = ../../../../Uncertified/Bsml/ocamlmake/OCamlMakefile
CC=$(MPICC)
OCAMLLDFLAGS=-cc $(CC)
LIBDIRS=../../../../Build/Extraction ../../../../Extraction ../../../../Uncertified/Bsml/src 
INCDIRS=../../../../Build/Extraction ../../../../Extraction ../../../../Uncertified/Bsml/src 
LIBS= Candidates bsmlcoq.mpi unix 
CFLAGS= -I$(OCAMLLIBPATH)  -O -g -Wall -fPIC
SOURCES= cand_run.ml
NO_CUSTOM=true
NCSUFFIX=.native
BCSUFFIX=.byte
RESULT=candidates
-include $(OCAMLMAKEFILE)
