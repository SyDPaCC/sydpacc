# SyDPaCC - SYSTEMATIC DEVELOPMENT OF PROGRAMS FOR PARALLEL AND CLOUD COMPUTING
# version 0.4

## Prerequisites

- The [Coq Proof Assistant](https://coq.inria.fr): Version 8.13 or higher
- An [OCaml](https://ocaml.org) compiler
- A C compiler and a MPI library such as [MPICH](https://www.mpich.org) or [Open MPI](https://www.open-mpi.org).

## Installation instructions

1. Compilation of the framework (requires only Coq):

   ``make``

1. Configure (checks all the additional requirements):

   ``cd config; ./configure; cd ..``


1. Compilation of the extracted and uncertified code:

   ``make -f Makefile.bsml``

1. Use ``mpirun`` to execute the compiled applications
   present in sub-directories of ``Uncertified/Applications``.

1. Documentation:

   ``make html``

   generates the documentation as html files in the
   directory ``html/``
