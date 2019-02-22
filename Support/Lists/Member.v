Require Import Coq.Lists.List. Import ListNotations.

(** * A boolean membership function on lists *)

Fixpoint mem {A:Type}(eq_dec:forall(a b:A),{a=b}+{~a=b})(a:A)(l:list A):bool:=
  match l with 
    | [] => false 
    | h::t => if (eq_dec h a) then true else mem eq_dec a t
  end.

Lemma In_mem_eq: 
  forall{A:Type}(eq_dec:forall(a b:A),{a=b}+{~a=b})(l:list A)(a:A),
    In a l <-> mem eq_dec a l = true.
Proof.
  intros A eqA l a; split; intro H.
  (* -> *)
  induction l as [_ | a' l]; simpl in *.
    elim H.
    destruct H.
      rewrite H; case_eq(eqA a a); intros H'; 
        auto; elim H'; apply eq_refl.
      rewrite IHl; case_eq(eqA a' a); auto. 
  (* <- *)
  induction l as [_ | a' l]; simpl in *.
    discriminate.
    destruct(eqA a' a); intuition.
Qed.

