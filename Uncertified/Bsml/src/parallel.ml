module Make : 
  functor (P : Bsmlsig.MACHINE_PARAMETERS) -> 
    functor (C : Bsmlsig.COMM) -> 
      Bsmlsig.BSML
=
  functor (Parameters : Bsmlsig.MACHINE_PARAMETERS) -> 
    functor (Comm : Bsmlsig.COMM) -> 
struct
  
  let _ = 
    begin
      Comm.initialize();
      at_exit Comm.finalize
    end

  type 'a par = 'a 
      
  let argv = Comm.argv()

  let parameters = 
    begin
      Parameters.read (Comm.nprocs());
      Parameters.get()
    end

  let bsp_p = parameters.Parameters.p
  let bsp_g = parameters.Parameters.g
  let bsp_l = parameters.Parameters.l
  let bsp_r = parameters.Parameters.r

  let mkpar f = f (Comm.pid())

  let apply f v = f v

  let put f = 
    let data = Array.init bsp_p (fun i->f i) in
    let res = Comm.send data in
      fun i -> res.(i)

  exception Invalid_processor of int
    
  let within_bounds n = (0<=n) && (n<bsp_p)

  let proj vb = 
    let data = 
      Array.init bsp_p (fun i->vb) in
    let res = Comm.send data in
      fun n->
	if not(within_bounds n)
	then raise (Invalid_processor n)
	else res.(n)
	  
  exception Timer_failure of string

  exception Parmatch_nextcase
  exception Parmatch_failure

  type timing_state = Running | Stopped

  let bsp_time_start = ref 0.

  let timing = ref Stopped

  let start_timing () = 
    if !timing=Stopped
    then 
      (bsp_time_start := Comm.wtime();
       timing := Running)
    else
      raise (Timer_failure "Timer is already running")

  let stop_timing () =
    if !timing=Running
    then 
      (bsp_time_start := (Comm.wtime()) -. (!bsp_time_start);
       timing:=Stopped)
    else
      raise (Timer_failure "Timer was not started!")

  let get_cost () = !bsp_time_start

  let abort error_code s = 
    print_string s;flush stdout;
    Comm.abort error_code;
    exit error_code
end
