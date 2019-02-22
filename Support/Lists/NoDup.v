Require Import Coq.Lists.List.
Import ListNotations.

(** * Additional property about [NoDup] *)

Lemma NoDup_map:
  forall A B (f:A->B) l,
    (forall x y, f x = f y -> x = y) ->
    NoDup l <-> NoDup (map f l).
Proof.
  intros A B f l H; split.
  - intro H_NoDup.
    induction l as [ | x xs IH ].
    + constructor.
    + simpl; constructor.
      * inversion H_NoDup as [ | x' xs' H1 H2 ]; subst.
        contradict H1.
        apply in_map_iff in H1.
        destruct H1 as [ x' [ Hf Hin] ].
        apply H in Hf; now subst.
      * apply IH; inversion H_NoDup as [ | x' xs' H1 H2 ]; now subst.
  - apply NoDup_map_inv.
Qed.
