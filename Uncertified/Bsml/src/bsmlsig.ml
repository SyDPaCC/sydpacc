(** Interface of all the main components of BSML.
    @author Louis Gesbert, Frédéric Gava, Frédéric Loulergue
*)


(** {2 BSML Primitives} *)

(** Interface of the modules implementing the BSML primitives *)

module type BSML =
sig


  (*******************************************************************)
  (** {3 Types} *)

  (** Abstract type for parallel vector of size p. 

      In the following we will note <v{_0}, ..., v{_p-1}> the parallel
      vector with value v{_i} at processor i *)
  type 'a par

  (*******************************************************************)
  (** {3 Machine parameters accessors} *)

  (** Returns the arguments from command line with implementation-specific
      arguments removed. *)
  val argv : string array 
    
  (** Number {i p} of processes in the parallel machine. *)
  val bsp_p : int

  val within_bounds: int -> bool
    (** [within_bounds n] is [true] is n is between 0 and {i p-1},
	[false] otherwise. *)

  (** BSP parameter {i g} of the parallel machine. *)  
  val bsp_g : float

  (** BSP parameter {i l} of the parallel machine. *)  
  val bsp_l : float

  (** BSP parameter {i r} of the parallel machine. *)  
  val bsp_r : float

  (*******************************************************************)
  (** {3 Exceptions} *)

  (** Raised when asked for a processor id that is not between [0] and
      [bsp_p] - 1. In particular, this exception can be raised by the
      functions that [proj] and [put] return. *)
  exception Invalid_processor of int

  exception Timer_failure of string

  (*******************************************************************)
  (** {3 Parallel operators} *)

  (** Parallel vector creation. {b Parameters :}
      - [f] function to evaluate in parallel
      @return the parallel vector with [f] applied to each pid:
      <[f 0], ..., [f (p-1)]> *)
  val mkpar : (int -> 'a) -> 'a par

  (** Pointwise parallel application. {b Parameters :}
      - [vf] a parallel vector of functions <f{_0}, ..., f{_p-1}>
      - [vv] a parallel vector of values <v{_0}, ..., v{_p-1}>
      @return the parallel vector <f{_0} v{_0}, ..., f{_p-1} v{_p-1}> *) 
  val apply : ('a -> 'b) par -> 'a par -> 'b par
  
  (** Global communication. {b Parameters :}
      - [f] = <f{_0}, ..., f{_p-1}>, f{_i} j is the value that processor
        [i] should send to processor [j].
      @return a parallel vector [g] = <g{_0}, ..., g{_p-1}> where g{_j} i = f{_i}
      j is the value received by processor [j] from processor [i].
  *)
  val put : (int -> 'a) par -> (int -> 'a) par 

  (** projection (dual of [mkpar]). Makes all the elements of a parallel vector
      global. {b Parameters :}
      - [v] a parallel vector <v{_0}, ..., v{_p-1}>
      @return a function f such that f i = v{_i} *)
  val proj : 'a par -> (int -> 'a)
  
  (** Aborts computation and quits. {b Parameters :}
      - [err] error code to return
      - [msg] message to print on standard error *)
  val abort : int -> string -> 'a

  val start_timing : unit -> unit
  val stop_timing : unit -> unit

  (** returns a parallel vector which contains, at each processor, the time
      elapsed between the calls to [start_timing] and [stop_timing].
      @raise Timer_failure if the call to one of those functions was meaningless
      ({e e.g.} [stop_timing] called before [start_timing]). *)
  val get_cost : unit -> float par
end

(** {2 Interface for modules providing BSP parameters} *)

(** Access to the machine parameters from a configuration file. *)

module type MACHINE_PARAMETERS =
sig

  (** Describes the BSP parameters of the machine. *)
  type bsp = {
    p:int;
    g:float;
    l:float;
    r:float
  }
  
  (** Reads the parameters from the configuration file.
      {b Parameters :}
      - [bsp_p] The current number of processors to choose among the possible configurations *)
      (* - [valid] function returning wether a read parameter is correct *)
  val read : int -> unit

  (** Get the current parameters.
      @return the value of the parameters as initialised by [read ()] *)
  val get : unit -> bsp
end

(** {2 Interface for low-level communication modules} *)

(**  Module providing the implementation of the communication functions *)

module type COMM =
sig
  (** Performs implementation-dependent initialization. Should be
      called only once in the course of a program *)
  val initialize : unit -> unit

  (** Performs implementation-dependent finalization. This will be
      called at the end of the program. *)
  val finalize : unit -> unit

  (** Returns the processor ID of the host processor *)
  val pid : unit -> int

  (** Returns the number of processors in the parallel machine *)
  val nprocs : unit -> int

  (** Returns the array of command-line arguments *)
  val argv : unit -> string array

  (** *)
  val send : 'a array -> 'a array

  (** Returns the clock *)
  val wtime : unit -> float

  (** Aborts the computation *)
  val abort : int -> unit
end
