Generalizable All Variables.
Require Import Coq.Lists.List. Import ListNotations.
Set Implicit Arguments.

(** * Additional lemmas on [List.map] and [List.flat_map] *)
Lemma map_assumption: 
  forall A B (l:list A) (f g:A->B),
    (forall x, In x l -> f x = g x) -> map f l = map g l.
Proof.
  intros A B; induction l; intros f g H.
  - trivial.
  - simpl; f_equal; intuition. 
Qed.

Lemma in_map_iff_inj: 
  forall A B (f:A->B)(l:list A), 
    (forall x y, f x = f y -> x = y) ->
    forall x, In x l <-> In (f x) (map f l).
Proof.
  induction l; intros Injective x; simpl; split; auto;
    intros [ H | H].
  - left; rewrite H; auto.
  - right; apply in_map; assumption.
  - left; apply Injective; assumption.
  - right; rewrite IHl; assumption.
Qed.

Lemma flatmap_app:
  forall A B (f:A->list B)(x y:list A),
    flat_map f (x ++ y) = flat_map f x ++ flat_map f y.
Proof.
  induction x.
  - trivial.
  - intro y. simpl.
    now rewrite <- List.app_assoc, IHx.
Qed.


(** * A terminal recursive version of [List.map]. *)
Fixpoint map_aux A B (f:A->B)(l:list A)(res:list B) : list B := 
  match l with 
    | [] => rev' res
    | x::xs => map_aux f xs ((f x)::res)
  end.

Definition map'  A B (f:A->B)(l:list A) : list B := map_aux f l [].

(** * Properties of terminal recursive version of [List.map]. *)
Lemma map_map_aux:
  forall  A B (f:A->B)(l:list A)(res:list B),
    (rev' res)++(map f l) = map_aux f l res.
Proof.
  induction l; intros res; simpl.
  - apply app_nil_r.
  - rewrite <- IHl. unfold rev'.
    repeat rewrite rev_append_rev,app_nil_r.
    simpl. now rewrite <- app_assoc. 
Qed.

Lemma map'_map:
    forall A B (f:A->B)(l:list A),
      map' f l = map f l.
Proof.
  induction l.
  - trivial.
  - unfold map'. 
    simpl. now rewrite <- map_map_aux.
Qed.

Lemma removelast_map:
  forall A B (f:A->B) l,
    removelast(map f l) = map f (removelast l).
Proof.
  intros A B f; induction l as [ | h t IH ].
  - trivial.
  - simpl; rewrite IH; destruct t; auto.
Qed.


