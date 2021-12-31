Require Import Coq.Lists.List Coq.Classes.EquivDec Lia. Import ListNotations.
Require Import SyDPaCC.Core.Bmf  SyDPaCC.Support.List.
Set Implicit Arguments.
Generalizable All Variables.

(* ---------------------------------------------------- *)

(** * Count *)

Section Count.

  Variable A : Type.
  Variable predicate : { pred: A -> bool & { a : A | pred a = true} }.
  Definition p : A->bool := projT1 predicate.
 
  (** ** Specification of the problem *)
  
  Definition count_spec (l:list A) : nat :=  
    length (filter p l).

  (** ** [count_spec] is both leftwards and rightwards *)
  
  Definition opl (a:A)(count:nat) : nat :=
    count + (if (p a) then 1 else 0). 
  
  Instance count_leftwards : Leftwards count_spec opl 0.
  Proof.
    constructor; induction l as [ | x xs IH ]; simpl.
    - trivial.
    - rewrite <- IH; clear IH; unfold opl, count_spec; simpl.
      destruct(p x); simpl; lia.
  Qed.

  Definition opr (count:nat)(a:A) : nat :=
    count + (if (p a) then 1 else 0). 
  
  Instance count_rightwards: Rightwards count_spec opr 0.
  Proof.
    constructor; induction l as [ | x xs IH ] using rev_ind; simpl.
    - trivial.
    - unfold count_spec in *; simpl.
      rewrite fold_left_app, filter_app; simpl.
      autorewrite with length. unfold opr at 1.
      destruct(p x); auto.
  Qed.

  (** ** [count_spec] has a weak right inverse if its predicate argument is
      true for at least one element *)

  Definition default : A := proj1_sig (projT2 predicate).
  Lemma default_prop : p default = true.
    unfold p, default; destruct predicate as [ p [ a Ha ]]; simpl;  auto.
  Qed.

  Definition count_inv (n:nat) : list A :=
    map(fun x=>default) (seq 0 n).

  Lemma length_filter_count_inv:
    forall n, length(filter p (count_inv n)) = n.
  Proof.
    intro; unfold count_inv.
    rewrite filter_true
      by (intros a Ha; rewrite in_map_iff in Ha; destruct Ha as [ y [ Heq _ ]];
          rewrite <- Heq; apply default_prop).
    now autorewrite with length.
  Qed.

  Hint Rewrite length_filter_count_inv : length.
  
  Instance count_right_inverse :
    Right_inverse count_spec count_inv.
  Proof.
    constructor; induction l as [|x xs IH].
    - trivial.
    - unfold count_spec; now autorewrite with length.
  Qed.

  (** ** [count_spec] is an homomorphism *)
  Global Instance count:
    Homomorphic count_spec
                (fun l r=>count_spec(count_inv l ++ count_inv r)).
  typeclasses eauto.
  Qed.
  
  (** ** Optimization of this homomophism *)
  
  Global Instance opt_op : Optimised_op count_spec.
  Proof.
    constructor; unfold count_spec; eexists.
    intros a b. rewrite filter_app;  autorewrite with length.
    reflexivity.
  Defined.

  Global Instance opt_f : Optimised_f count_spec.
  Proof.
    constructor; unfold count_spec; eexists; intro a; simpl.
    replace(length (if p a then [a] else [])) with (if p a then 1 else 0).
    reflexivity.
    destruct(p a);auto.
  Defined.

End Count.
