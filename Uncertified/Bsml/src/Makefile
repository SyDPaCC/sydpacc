-include ../../../config/Makefile.config
OCAMLMAKEFILE = ../ocamlmake/OCamlMakefile
CC=$(MPICC)
CFLAGS= -I$(OCAMLLIBPATH)  -O -g -Wall -fPIC
LFLAGS= -warn-error -a
SOURCES= ../../../Extraction/BinNums.ml ../../../Extraction/Core.ml ../../../Uncertified/NatInt/nint.ml bsmlsig.ml parameters_in_file.ml parallel.ml comm_mpi.c mpi.mli mpi.ml bsmlmpi.ml bsmlWrapperN.ml
RESULT= bsmlcoq.mpi
-include $(OCAMLMAKEFILE)
