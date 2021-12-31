Require Import NArith.

(** * Specification of the Bulk Synchronous Parallel ML Library *)

(** ** BSP Parameters *)

(** In the BSP model, a parallel machine is characterised by four
    parameters. In our Coq formalisation, we currently consider only
    one parameter: the number of pids. Traditionnaly in the BSP
    literature, this parameter is called [p]. The module type
    [BSP_PARAMETERS] is thus a module containing this parameter, that
    is assumed to be a stricly positive natural. *)

Open Scope N_scope.

Module Type BSP_PARAMETERS.  

  Parameter p : N.  
  Axiom p_spec : 0 < p.

End BSP_PARAMETERS.

(** ** The BSML Library *)

Module Type BSML.

  Declare Module Bsp : BSP_PARAMETERS.

  (** *** The Parallel Data Structure: Parallel Vector *)

  (** A process identifier or [pid] is a natural number smaller than
      the number of processors of the parallel machine. *)
  
  Notation pid := { n:N | N.ltb n Bsp.p = true }.

  (** A parallel vector is an abstract type: it is possible 
      (in specifications only) to observe the value of 
      a parallel vector at a specific processor. *)

  (** Informally, a parallel vector is written <v_0, ..., v_p-1>*)
      
  Section Parallel_vectors.

    Parameter par : Type -> Type.

    Parameter get: 
      forall {A: Type}, par A -> pid -> A.

    Axiom par_eq : forall {A:Type} (v v': par A),
      (forall (i: pid), get v i = get v' i) -> 
      v = v'.

  End Parallel_vectors.

  (** *** BSML Primitives on Parallel Vectors *)
  
  Section Primitives.

    (** [mkpar] builds a parallel vector from a function that
        describes the value to be held be each processor. *)
    Parameter mkpar: 
      forall {A:Type} (f:pid -> A), par A.

    (** Informally, [mkpar f] = <f 0, ..., f(p-1)> *)
    Axiom mkpar_spec: 
      forall (A:Type)(f:pid->A)(i:pid),
        get (mkpar f) i = f i.

    (** [apply] applies a parallel vector of functions to a parallel
        vector of values *)
    Parameter apply: 
      forall {A B: Type}(vf: par(A->B))(vx:par A), par B.

    (** Informally, [apply] <f_0, ..., f_p-1> <x_0, ..., x_p-1> = 
                            <f_0 x_0, ..., f_p-1 x_p-1> *)
    Axiom apply_spec:
      forall (A B: Type) (vf: par (A -> B)) (vx: par A)
             (i: pid),
        get (apply vf vx) i = (get vf i) (get vx i).

    (** [put] is a communication function. It takes as input a
        parallel vector of functions and returns a vector of the same
        type. In the input vector, each function encodes the messages
        to be sent to each other processor. In the output vector, each
        function encodes the messages received from other
        processors. *)
    Parameter put: 
      forall {A:Type}(vf:par(pid->A)),
        par(pid->A).

    (** Informally, [put] <f_0, ..., f_p-1> = 
                          <[fun i =>f_i 0], ..., [fun i =>f_i (p-1)]> *) 
    Axiom put_spec:
      forall (A:Type)(vf:par(pid->A))
             (i j:pid),
        get (put vf) i j = get vf j i.

    (** [proj] is also a communication function. It is the dual of [mkpar] *)
    Parameter proj: 
      forall {A:Type}(v: par A), pid -> A.

    (** Informally, [proj] <x_0, ..., x_p-1> = [fun i => x_i] *)
    Axiom proj_spec:
      forall (A:Type)(v: par A)(i: pid), 
        (proj v) i = get v i.

  End Primitives.

  #[export] Hint Rewrite mkpar_spec apply_spec put_spec proj_spec: bsml.

  #[export] Hint Resolve par_eq : bsml.

End BSML.
