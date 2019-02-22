Generalizable All Variables.
Require Import Coq.Lists.List Coq.Classes.EquivDec. Import ListNotations.
Set Implicit Arguments.


Fixpoint assoc A B `{eq_dec:EqDec A eqA} (a:A) (l:list (A * B)) : option B :=
  match l with 
    | [ ] => None
    | h::t => if (eq_dec a (fst h)) then Some (snd h) else assoc a t
  end.

Lemma assoc_in:
  forall (A B:Type){eqA: EqDec A eq}(a:A) l (b:B),
    assoc a l = Some b -> In (a,b) l.
Proof.
  intros A B eqA a l; revert a; induction l as [ | h t IH ];
    intros a b H; simpl in H.
  - discriminate.
  - destruct (eqA a (fst h)) as [ Heq | Hneq ].
    + rewrite Heq; inversion H; subst.
      rewrite <- surjective_pairing; simpl; auto.
    + simpl; right; now apply IH.
Qed.

Lemma assoc_not_in:
  forall (A B:Type){eqA: EqDec A eq}(l:list(A*B)) a,
    ~(In a (map fst l)) ->
    assoc a l = None.
Proof.
  intros A B eqA; induction l as [ | h t IH ]; intros a Hin.
  - trivial.
  - simpl.
    destruct(eqA a (fst h)) as [ Heq | Hneq ].
    + contradict Hin; simpl; left; now rewrite Heq.
    + apply IH; contradict Hin; simpl; auto.
Qed.

Lemma assoc_app: 
  forall (A B: Type){eqA: EqDec A eq}(a:A)(l1 l2:list (A*B)),
    (forall b, ~In (a,b) l1) -> assoc a (l1++l2) = assoc a l2.
Proof.
  intros A B eqA a; induction l1; intros l2 H.
  - trivial.
  - simpl; destruct (eqA a (fst a0)) as [ Heq | Hneq ].
    + specialize (H (snd a0)); rewrite Heq in H.
      rewrite <- surjective_pairing in H.
      contradict H; simpl; auto.
    + apply IHl1; intros b Hb; apply (H b); right; assumption.
Qed.

Inductive in_first (A B: Type)(x:(A*B)) : list (A*B) -> Prop :=
  in_first_:
    forall l1 l2 l,
      (forall b, ~(In ((fst x),b) l1)) ->
      l = l1++x::l2 ->
      in_first x l.

Lemma assoc_in_first: 
  forall (A B:Type)(eqA: EqDec A eq)(a:A)(l:list (A*B))(b:B),
    assoc a l = Some b <-> in_first (a,b) l.
Proof.
  intros A B eqA a l; revert  a; induction l; split; intro H; simpl in H.
  - discriminate.
  - inversion H as [ l1 l2 H3 H1 H2 ]; subst.
    apply app_cons_not_nil in H2; now exfalso.
  - case_eq (eqA a0 (fst a)); intros Heq Heq'; rewrite Heq' in H; simpl in H.          (* Case a0 = fst a *)
    inversion H; rewrite Heq in *; destruct a; simpl.
    + simpl in *; inversion H; subst.
      apply in_first_ with (l1:=[])(l2:=l); intros; auto.
    + specialize (IHl a0 b); apply IHl in H.
      inversion H as [ l1 l2 HH H1 H2 ]; subst.
      rewrite app_comm_cons.
      apply in_first_ with (l1:=(a::l1))(l2:=l2); auto; intros b' Hin.
      specialize (H1 b'); apply H1; simpl in Hin.
      destruct Hin as [ H' | Hin ]; subst; auto.
      simpl in *. clear Heq'; now elim Heq.
  - inversion H as [ l1 l2 HH H1 H2]; subst.
    rewrite H2, assoc_app by auto; simpl.
    clear; case_eq(eqA a0 a0); intros H; auto; now elim H.
Qed.