Require Import Coq.Lists.List. Import ListNotations.
Require Import NArith Omega.

Open Scope N_scope.

(** * List length that returns a [N] *)

(** A length function that returns a value of type [N]. *)
Fixpoint length (A:Type)(l:list A) : N := 
  match l with 
    | [] => 0 
    | h::t => 1 + length A t
  end.

Arguments length [A].

Fact length_cons:
  forall A (x:A) xs,
    length(x::xs) = 1 + length xs.
  auto. Qed.

Fact length_nil:
  forall A (x:A) xs,
    not (@length A []  = length(x::xs)).
  intros. intro H.
  rewrite length_cons in H.
  simpl in H.
  destruct (length xs); zify; omega.
Qed.

Hint Rewrite length_cons : length.

Hint Rewrite <- N.add_1_l : length.

(** [List.length] returns the same value than [length], up to
    conversion from [nat] to [N]. *)
Lemma length_Nlength:
  forall (A:Type)(l:list A),
    List.length l = nat_of_N (length l).
Proof.
  intros A; induction l as [ | x xs IH ].
  - trivial.
  - replace(length(x::xs)) with (1+length xs) by auto.
    rewrite N2Nat.inj_add.
    simpl; auto using IH.
Qed.

(** [length] returns the same value than [List.length], up to
    conversion from [N] to [nat]. *)
Lemma Nlength_length:
  forall (A:Type)(l:list A),
    length l = N_of_nat (List.length l).
Proof.
  intros A; induction l as [ | x xs IH ].
  - trivial.
  - replace(List.length(x::xs)) with(S(List.length xs)) by auto.
    rewrite Nat2N.inj_succ.
    now rewrite <- IH, <- N.add_1_l.
Qed.

Lemma map_length:
  forall {A B} (f:A->B) l,
    length(map f l) = length l.
Proof.
  intros A B f l.
  repeat rewrite Nlength_length; f_equal.
  apply List.map_length.
Qed.

Lemma app_length:
  forall {A} (l1 l2:list A),
    length(l1 ++ l2) = length l1 + length l2.
Proof.
  intros A l1 l2.
  repeat rewrite Nlength_length.
  rewrite List.app_length.
  zify; omega.
Qed.

Hint Rewrite @map_length @app_length : length.

Close Scope N_scope.