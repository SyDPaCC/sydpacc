external pid : unit -> int = "bsmlimpl_pid"

external nprocs : unit -> int = "bsmlimpl_nprocs"

external mpi_initialize : string array -> unit = "ocaml_mpi_init" 

let argv () = Sys.argv

let initialize () = mpi_initialize (argv())

external finalize : unit -> unit = "bsmlimpl_finalize"

external alltoall_int_array:
    int array -> int array -> unit
    = "bsmlimpl_alltoall_int"
let alltoall_int_array src dst =
  if Array.length dst <> Array.length src 
  then failwith "MPI.alltoall_int_array: array size mismatch"
  else alltoall_int_array src dst 

external alltoall_string:
  string -> int array -> string -> int array -> unit
  = "bsmlimpl_alltoall"

let send data  = 
  if Array.length data <> (nprocs())
  then failwith ("Mpi.alltoall: wrong array size "^
		   (string_of_int(Array.length data))^
		   " instead of "^
		   (string_of_int (nprocs())));
  let buffers =
    Array.map (fun d -> Marshal.to_string d [Marshal.Closures]) data in
  (* Determine lengths of strings *)
  let sendlengths = Array.map String.length buffers in
  let total_len = Array.fold_left (+) 0 sendlengths in
  let send_buffer = String.create total_len in
  let pos = ref 0 in
  for i = 0 to (nprocs()) - 1 do
    String.blit buffers.(i) 0 send_buffer !pos sendlengths.(i);
    pos := !pos + sendlengths.(i)
  done;
  let recvlengths = Array.create (nprocs()) 0 in
  (* Alltoall those lengths *)
  alltoall_int_array sendlengths recvlengths;
  let total_len = Array.fold_left (+) 0 recvlengths in
  (* Allocate receive buffer *)
  let recv_buffer = String.create total_len in
  (* Do the alltoall *)
  alltoall_string send_buffer sendlengths recv_buffer recvlengths;
  (* Build array of results *)
  let res0= Marshal.from_string recv_buffer 0 in
  let res = Array.make (nprocs()) res0 in
  let pos = ref 0 in
  for i = 1 to (nprocs()) - 1 do
    pos := !pos + recvlengths.(i - 1);
    res.(i) <- Marshal.from_string recv_buffer !pos
  done;
  res

external wtime: unit -> float = "bsmlimpl_wtime" 

external abort: int -> unit = "bsmlimpl_abort"
