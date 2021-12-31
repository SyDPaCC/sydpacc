Generalizable All Variables.
Require Import Coq.Lists.List. Import ListNotations.
Set Implicit Arguments.

(** * A terminal recursive version of [List.combine]. *)
Fixpoint combine_aux A B (l:list A)(l':list B) (res:list (A*B)) : list (A*B) := 
  match (l,l') with 
    | (x::xs, y::ys) =>
      combine_aux xs ys ((x,y)::res)
    | _ => rev' res
  end.

Definition combine'  A B (l:list A)(l':list B) : list (A*B) :=
  combine_aux l l' [].

Lemma combine_aux_prop:
  forall A B (l:list A)(l':list B) acc,
    combine_aux l l' acc = rev' acc ++ combine l l'.
Proof.
  intros A B l;
    induction l as [| x xs IHx];
    intros l' acc; destruct l' as [ | y ys ];
      simpl; autorewrite with list; trivial.
  rewrite IHx. unfold rev'. simpl.
  repeat rewrite rev_append_rev.
  repeat rewrite <- app_assoc.
  trivial.
Qed.
  
Lemma combine'_combine:
  forall A B (l:list A) (l':list B),
    combine' l l' = combine l l'.
Proof.
  intros A B l l'. unfold combine'.
  apply combine_aux_prop.
Qed.