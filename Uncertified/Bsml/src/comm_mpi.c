#include <mpi.h>
#include <stdio.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include "comm_mpi.h"

int pid, nprocs;

value bsmlimpl_nprocs(value unit) 
{
  CAMLparam1(unit);
  CAMLreturn(Val_int(nprocs));
}

value bsmlimpl_pid(value unit) 
{
  CAMLparam1(unit);
  CAMLreturn(Val_int(pid));
}

value ocaml_mpi_init(value arguments)
{
  int argc, i;
  char ** argv;

  CAMLparam1 (arguments);
  argc = Wosize_val(arguments);
  argv = (char**)stat_alloc((argc + 1) * sizeof(char *));
  for (i = 0; i < argc; i++) argv[i] = String_val(Field(arguments, i));
  argv[i] = NULL;
  MPI_Init(&argc, &argv);
  MPI_Comm_rank(MPI_COMM_WORLD, &pid);
  MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
  CAMLreturn(Val_unit);
}

value bsmlimpl_finalize(value unit)
{
  CAMLparam1(unit);
  MPI_Finalize();
  CAMLreturn(Val_unit);
}

value bsmlimpl_alltoall_int(value data, value result)
{
  CAMLparam2(data,result);
  MPI_Alltoall(&Field(data, 0), 1, MPI_LONG,
	       &Field(result, 0), 1, MPI_LONG,
	       MPI_COMM_WORLD);
  CAMLreturn(Val_unit);
} 

static void caml_mpi_counts_displs(value lengths,
                                   /* out */ int ** counts,
                                   /* out */ int ** displs)
{
  int size, disp, i;

  size = Wosize_val(lengths);
  if (size > 0) {
    *counts = stat_alloc(size * sizeof(int));
    *displs = stat_alloc(size * sizeof(int));
    for (i = 0, disp = 0; i < size; i++) {
      (*counts)[i] = Int_val(Field(lengths, i));
      (*displs)[i] = disp;
      disp += (*counts)[i];
    }
  } else {
    *counts = NULL;
    *displs = NULL;
  }
}

value bsmlimpl_alltoall(value sendbuf, value sendlengths,
			value recvbuf, value recvlengths)
{
  int * recvcounts, * recvdispls;
  int * sendcounts, * senddispls;
  
  CAMLparam4(sendbuf,sendlengths,recvbuf,recvlengths);
  caml_mpi_counts_displs(sendlengths, &sendcounts, &senddispls);
  caml_mpi_counts_displs(recvlengths, &recvcounts, &recvdispls);
  MPI_Alltoallv(String_val(sendbuf), sendcounts, senddispls, MPI_BYTE,
		String_val(recvbuf), recvcounts, recvdispls, MPI_BYTE,
		MPI_COMM_WORLD);
  if (recvcounts != NULL) {
    stat_free(recvcounts);
    stat_free(recvdispls);
  }
  if (sendcounts != NULL) {
    stat_free(sendcounts);
    stat_free(senddispls);
  }
  CAMLreturn(Val_unit);
}


value bsmlimpl_wtime(value unit)
{
  CAMLparam1(unit);
  CAMLreturn(copy_double(MPI_Wtime()));
}

value bsmlimpl_abort(value errorcode)
{
  CAMLparam1(errorcode);
  MPI_Abort(MPI_COMM_WORLD,Int_val(errorcode));
  CAMLreturn(Val_unit);
}
