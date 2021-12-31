-include ../../../../config/Makefile.config
OCAMLMAKEFILE = ../../../../Uncertified/Bsml/ocamlmake/OCamlMakefile
CC=$(MPICC)
OCAMLLDFLAGS=-cc $(CC)
# LIBDIRS=../../../../Build/Extraction ../../../../Extraction ../../../../Uncertified/Bsml/src 
# INCDIRS=../../../../Build/Extraction ../../../../Extraction ../../../../Uncertified/Bsml/src 
LIBDIRS=../../../../Build/Extraction ../../../../Uncertified/Bsml/src 
INCDIRS=../../../../Build/Extraction ../../../../Uncertified/Bsml/src 
LIBS= bsmlcoq.mpi unix 
CFLAGS= -I$(OCAMLLIBPATH)  -O -g -Wall -fPIC
SOURCES= generate.ml
NO_CUSTOM=true
NCSUFFIX=.native
BCSUFFIX=.byte
RESULT=generate
-include $(OCAMLMAKEFILE)
