Require Import Coq.Lists.List Program NArith. Import ListNotations.
Require Import SyDPaCC.Support.List.
Require Import SyDPaCC.Core.Bmf SyDPaCC.Core.Parallelization.
From SyDPaCC.Bsml.Model Require Import Core Pid.
Set Implicit Arguments.

(** * Distributed Lists *)

(** In order to automatically parallelize applications, it is
    necessary to proof the correspondence between parallel
    datastructures and sequential datastructures. *)

(** Distributed lists are implemented as parallel vectors of lists and
    are shown to correspond to sequential lists.  The correspondence
    is obtained simply by taking the contatenation of the lists hold
    by the processors. *)

(** ** Type Correspondence Implementation *)
Module C(Import Bsml: BSML)(Import Pid : Pid.TYPE Bsml.Bsp).

  Program Definition join A (v:par(list A)) :=
    List.flat_map (proj v) pids.
  
  #[export] Program Instance surjective_join (A:Type) : Surjective (join (A:=A)).
  Next Obligation.
    set(v := mkpar(fun pid =>if pid_dec first pid then y else [])).
    exists v. unfold join. apply pids_ind.
    - unfold v; simpl; autorewrite with bsml.
      case_eq(pid_dec first first);intros H _.
      + apply app_nil_r.
      + now contradict H.
    - intros i Hi IH. rewrite pid_up_to_succ.
      rewrite flatmap_app, IH. unfold v.
      simpl. autorewrite with bsml. 
      case_eq(pid_dec first (succ Hi));intros H _. 
      + assert( N.succ (` i) = 0) as HH.
        {
          replace 0 with (` first) by auto.
          now rewrite H.
        }
        apply N.succ_0_discr in HH.
        now exfalso.
      + now repeat rewrite right_neutral.
  Qed.

  #[export] Program Instance list_par_list_corr A :
    TypeCorr (@join A).

  (** * Precondition: Same Distribution *)

  Class SameDistribution A B (v1:par(list A))(v2:par(list B)) :=
    {
      same_distribution: forall (i:pid), length(get v1 i) = length(get v2 i)
    }.

  Generalizable All Variables.

  #[export] Instance sd_par2prop
           `{TypeCorr (list A) (par(list A)) }
           `{TypeCorr (list B) (par(list B))} :
    Par2Prop (@SameDistribution A B) := { }.

End C.

(** ** Module Type *)
Module Type T (Bsml: BSML)(Pid: Pid.TYPE Bsml.Bsp).
  Include C Bsml Pid.
End T.
