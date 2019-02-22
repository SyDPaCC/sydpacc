Require Import Coq.Lists.List.
Import ListNotations.

(** * Additional property about [List.seq] *)

Lemma seq_S_len :
  forall start len, 
    seq start (S len) = seq start len ++ [start+len].
Proof.
  induction len.
  - simpl; f_equal; auto.
  - simpl. repeat rewrite <- seq_shift.
    replace (map S (seq start len) ++ [start + S len]) 
    with (map S (seq start (S len))) by
        (rewrite IHlen, map_app; simpl; repeat f_equal; auto with arith).
    repeat rewrite seq_shift.
    auto.
Qed.