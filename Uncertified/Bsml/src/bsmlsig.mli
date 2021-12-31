module type BSML =
  sig
    type 'a par
    val argv : string array
    val bsp_p : int
    val within_bounds : int -> bool
    val bsp_g : float
    val bsp_l : float
    val bsp_r : float
    exception Invalid_processor of int
    exception Timer_failure of string
    val mkpar : (int -> 'a) -> 'a par
    val apply : ('a -> 'b) par -> 'a par -> 'b par
    val put : (int -> 'a) par -> (int -> 'a) par
    val proj : 'a par -> int -> 'a
    val abort : int -> string -> 'a
    val start_timing : unit -> unit
    val stop_timing : unit -> unit
    val get_cost : unit -> float par
  end
module type MACHINE_PARAMETERS =
  sig
    type bsp = { p : int; g : float; l : float; r : float; }
    val read : int -> unit
    val get : unit -> bsp
  end
module type COMM =
  sig
    val initialize : unit -> unit
    val finalize : unit -> unit
    val pid : unit -> int
    val nprocs : unit -> int
    val argv : unit -> string array
    val send : 'a array -> 'a array
    val wtime : unit -> float
    val abort : int -> unit
  end
