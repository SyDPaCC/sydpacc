Require Import Coq.Lists.List NArith. Import ListNotations.
Require Import SyDPaCC.Support.List.
From SyDPaCC.Bsml.Model Require Import Core Pid.
Set Implicit Arguments.

Module Make(Import Bsml: BSML)(Import Pid: Pid.TYPE Bsml.Bsp).

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

  #[export] Hint Rewrite replicate_spec parfun_spec : bsml.
  
  Lemma parfun_ext:
    forall A B (f g:A->B) v,
      (forall a, f a = g a) -> parfun f v = parfun g v.
  Proof.
    intros A B f g v H; apply par_eq; intro i;
      autorewrite with bsml; now apply H.
  Qed.
  
  Definition parfun2 A B C (f:A->B->C)(v:par A)(v':par B) : par C :=
    apply (parfun f v) v'.
  #[export] Hint Unfold parfun2 : bsml.

  Lemma parfun2_spec:
    forall A B C (f:A->B->C) v v' i, get(parfun2 f v v') i=f(get v i)(get v' i).
  Proof.
    intros; now repeat autounfold with bsml; autorewrite with bsml.
  Qed.

  #[export] Hint Rewrite parfun2_spec : bsml.
  
  Definition put_list A (data: par(list(pid*A))) : par(list A) :=
    let msg := parfun 
                 (fun listDstValue dst => assoc dst listDstValue)
                 data in
    let is_some := fun (x:option A) => match x with Some _ => true | _ => false end in
    parfun (fun f => filter_map_some f Pid.pids) (put msg).
  #[export] Hint Unfold put_list : bsml.
  
  Lemma put_list_spec:
    forall A v i (value:A),
      In value (get (put_list v) i) <-> exists j, in_first (i, value) (get v j).
  Proof.
    assert(forall A l x, In x l <-> In (Some x) (map (@Some A) l)) as Hsome
        by (intros; apply in_map_iff_inj; intros a b H; inversion H; trivial).
    intros A v i value; split; autounfold with bsml; autorewrite with bsml;
      rewrite Hsome, filter_map_some_prop, filter_In, in_map_iff; intro H.
    - destruct H as [ [ src  [ H1 H2] ] H3].
      autorewrite with bsml in H1.
      exists src. rewrite <- assoc_in_first; exact H1.
    - destruct H as [j Hj]; split; auto; exists j; split; autorewrite with bsml.
      + now rewrite assoc_in_first.
      + apply pids_spec.
  Qed.
  #[export] Hint Rewrite put_list_spec: bsml.
  
End Make.

Module Type TYPE (Import Bsml: BSML)(Import Pid : Pid.TYPE Bsml.Bsp).
  Include Make Bsml Pid.
End TYPE.
  
