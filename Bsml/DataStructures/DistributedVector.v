Require Import Coq.Lists.List Program NArith. Import ListNotations.
Require Import SyDPaCC.Support.UIP.
Require Import SyDPaCC.Support.NList.
Require Import SyDPaCC.Support.List.
Require Import SyDPaCC.Core.Bmf SyDPaCC.Core.Parallelization.
From SyDPaCC.Bsml.Model Require Import Core Pid.
Set Implicit Arguments.

(** * Distributed Vectors *)

(** In order to automatically parallelize applications, it is
    necessary to proof the correspondence between parallel
    datastructures and sequential datastructures. *)

(** Distributed vectors are implemented as parallel vectors of lists and
    are shown to correspond to sequential lists.  The correspondence
    is obtained simply by taking the contatenation of the lists hold
    by the processors. *)

(** ** Type Correspondence Implementation *)
Module C(Import Bsml: BSML)(Import Pid : Pid.TYPE Bsml.Bsp).

  Definition join A (v:par A) : { l : list A | length l = Bsp.p }.
    exists (List.map (proj v) pids).
    now autorewrite with length.
  Defined.

  Lemma list_length_inj:
    forall A (l l':list A)(Hl: length l = Bsp.p)(Hl': length l' = Bsp.p),
      l = l' ->
      exist (fun l=>length l=Bsp.p) l Hl = exist _ l' Hl'.
  Proof.
    intros A l l' Hl Hl' H.
    revert Hl; rewrite H. intro.
    assert(Hl = Hl') as HH by apply N.UIP.
    now rewrite HH.
  Qed.    

  Global Instance surjective_join (A:Type) : Surjective (join (A:=A)).
  Proof.
    constructor; intros [ l Hl ]; simpl.
    assert(NonEmpty l) as H
        by (constructor; destruct l; pid; intro; discriminate).
    set(v := mkpar(fun pid =>nth (proj1_sig pid) l (hd l))).
    exists v; unfold join; apply list_length_inj.
    rewrite nth_seq with (d:=hd l). rewrite Hl, <- pids_seq.
    apply pids_ind.
    - unfold v; simpl; autorewrite with bsml; auto.
    - intros i Hlast IH. rewrite map_map.
      apply map_ext; intro j; unfold v.
      now autorewrite with bsml.
  Qed.

  Global Program Instance list_par_list_corr A :
    TypeCorr (@join A).

End C.

(** ** Module Type *)
Module Type T (Bsml: BSML)(Pid: Pid.TYPE Bsml.Bsp).
  Include C Bsml Pid.
End T.