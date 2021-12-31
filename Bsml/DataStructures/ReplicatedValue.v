Require Import Coq.Lists.List Program. Import ListNotations.
Require Import SyDPaCC.Support.List.
Require Import SyDPaCC.Core.Bmf SyDPaCC.Core.Parallelization.
Require Import SyDPaCC.Bsml.Model.Core SyDPaCC.Bsml.Model.Pid.
Set Implicit Arguments.

(** * Replicated Values *)

(** In order to automatically parallelize applications, it is
    necessary to proof the correspondence between parallel
    datastructures and sequential datastructures. *)

(** ** Type Correspondence Implementation *)

(** Replicated Values are implemented as parallel vectors of values
    such that the same value is hold by each processor.  Replicated
    values are shown to correspond to the sequential type of the
    value.  The correspondence is obtained simply by taking the value
    that is replicated. *)

Module C(Import Bsml: BSML)(Import Pid : Pid.TYPE Bsml.Bsp).

  Program Definition join A (r:{v:par A|forall i,get v i=get v first}) : A :=
    (proj (` r)) first.
  
  Global Program Instance surjective_join (A:Type) : Surjective (join (A:=A)).
  Next Obligation.
    set(v := mkpar(fun _=> y)).
    assert(forall i, get v i = get v first) as Hv
        by now (intro i; unfold v; autorewrite with bsml).
    exists(exist (fun (v:par A)=>forall i, get v i=get v first) v Hv).
    unfold join, v.
    now simpl; autorewrite with bsml.
  Qed.

  Global Program Instance replicate_par_corr A :
    TypeCorr (@join A).

End C.

(** ** Module Type *)

Module Type T (Bsml: BSML)(Pid: Pid.TYPE Bsml.Bsp).
  Include C Bsml Pid.
End T.
