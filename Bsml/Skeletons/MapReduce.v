Require Import Coq.Lists.List Program. Import ListNotations.
Require Import SyDPaCC.Support.List.
From SyDPaCC.Core Require Import Bmf Parallelization.
From SyDPaCC.Bsml.Model Require Import Core Pid.
From SyDPaCC.Bsml.Skeletons Require Import StdLib.
From SyDPaCC.Bsml.DataStructures Require Import DistributedList ReplicatedValue.
Set Implicit Arguments.

(** * Parallel versions of [map] and [reduce] *)

(** In order to automatically parallelize applications, it is
    necessary to provide parallel functions and to show their
    correspondence with sequential functions. *)

(** We provide:

    - [par_map] that corresponds to [List.map]

    - [par_reduce] that corresponds to [reduce] (the result is a scalar)

    - [par_reduce'] that corresponds to [reduce] (the result is a parallel vector: a replicated value)
*)

Module Make(Import Bsml: BSML)(Import Pid: Pid.TYPE Bsml.Bsp)(Import StdLib: StdLib.TYPE Bsml Pid)
       (Import PL : DistributedList.T Bsml Pid)(Import RP: ReplicatedValue.T Bsml Pid).


  Definition replicate A (x:A) : par A :=
    mkpar(fun _ => x).
  #[export] Hint Unfold replicate : bsml.
  
  Lemma replicate_spec:
    forall A (x:A) i, get (replicate x) i = x.
  Proof.
    intros; now  autounfold with bsml; autorewrite with bsml.
  Qed.

  Definition parfun A B (f:A->B)(v:par A) : par B :=
    apply (replicate f) v.
  #[export] Hint Unfold parfun : bsml.

  Lemma parfun_spec:
    forall A B (f:A->B) v i, get(parfun f v) i=f(get v i).
  Proof.
    intros; now repeat autounfold with bsml; autorewrite with bsml.
  Qed.
  
  (** ** Parallel [map] *)
  Definition par_map (A B:Type)(f:A->B) : par(list A)->par(list B) := 
    parfun (map' f).
  #[export] Hint Unfold par_map : bsml.
  #[export] Hint Rewrite replicate_spec parfun_spec : bsml.
  #[export] Hint Rewrite map'_map map_app flatmap_app @reduce_app: bsml.

  (** [par_map] is a parallel version of [List.map]. *)
  #[export] Program Instance  map_par_map A B (f:A->B) : FunCorr (map f) (par_map f).
  Next Obligation.
    unfold PL.join.  apply pids_ind.
    - simpl; autounfold with bsml; now autorewrite with bsml.
    - intros n Hn IH; rewrite pid_up_to_succ.
      autorewrite with bsml; rewrite IH.
      autounfold with bsml; f_equal; simpl; now autorewrite with bsml.
  Qed.

  (*
  Instance sd_map A B (f:A->B) v : SameDistribution v (par_map f v).
  Proof.
    constructor; intro pid; unfold par_map.
    now autorewrite with bsml length.
  Qed.
   *)
  
  Unset Implicit Arguments.
  Generalizable All Variables.
 
  (** ** Parallel [reduce] *)
  Definition par_reduce {A}(op:A->A->A){e:A}{H:Monoid op e}(v:par(list A)) : A :=
    let local := parfun (reduce op) v in       (* local reductions *)
    let list  := List.map (proj local) pids in (* vector -> list   *)
    reduce op list.         (* reduction of the partial reductions *)
  #[export] Hint Unfold par_reduce : bsml.

  (** [par_reduce] is a parallel version of [reduce]. *)
  #[export] Program Instance reduce_par_reduce `(op:A->A->A) `{Monoid A op e} :
    FunCorr (reduce op) (par_reduce op).
  Next Obligation.
    unfold PL.join, par_reduce; apply pids_ind.
    - repeat autounfold with bsml; autorewrite with bsml; unfold reduce; simpl.
      rewrite left_neutral, right_neutral. now autorewrite with bsml.
    - intros n Hn IH; rewrite pid_up_to_succ.
      autorewrite with bsml. autounfold in * ;rewrite IH.
      f_equal. unfold reduce; simpl.
      autorewrite with bsml.
      now rewrite left_neutral, right_neutral.
  Qed.
  
  (** [par_reduce'] returns a parallel vector where all the processor
      hold the same value. *)
  Program Definition par_reduce' {A}(op:A->A->A){e:A}{H:Monoid op e}
    (v: par(list A)) : {v:par A | forall i, get v i = get v first } :=
    let local := parfun (reduce op) v in
    let msgs  := put(apply(mkpar(fun pid msg dst=>msg)) local) in
    let lists := parfun (fun f=>List.map f pids) msgs in
    parfun (reduce op) lists.
  Next Obligation.
    autorewrite with bsml. apply pids_ind.
    - autounfold with bsml; simpl;
      repeat rewrite left_neutral;
      now autorewrite with bsml.
    - intros i' Hi' IH; rewrite pid_up_to_succ.
      autorewrite with bsml; autounfold in *. rewrite IH; f_equal.
      autounfold with bsml; simpl;
      repeat rewrite left_neutral;
      now autorewrite with bsml.
  Qed.
  #[export] Hint Unfold par_reduce' : bsml.

  (** [par_reduce'] is a parallel version of [reduce]. *)
  #[export] Program Instance reduce_par_reduce' `(op:A->A->A) `{Monoid A op e} :
    FunCorr (reduce op) (par_reduce' op).
  Next Obligation.
    unfold PL.join, RP.join, par_reduce';
    autounfold with bsml; simpl; autorewrite with bsml;
    apply pids_ind.
    - simpl; autorewrite with bsml; unfold reduce; simpl;
      now rewrite left_neutral, right_neutral.
    - intros n Hn IH; rewrite pid_up_to_succ.
      autorewrite with bsml. rewrite IH.
      f_equal. unfold reduce; simpl.
      autorewrite with bsml.
      now rewrite left_neutral, right_neutral.
  Qed.

End Make.
