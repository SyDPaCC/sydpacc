Require Import Coq.Lists.List. Import ListNotations.

Set Implicit Arguments.

(** * Additional properties of [List.filter] *)
Lemma filter_app (E:Type) (f:E -> bool)(l1 l2 : list E) : 
  filter f (l1 ++ l2) = filter f  l1++(filter f l2).
Proof.
  induction l1 as [ | a l1 IH].
  - trivial.
  - simpl; rewrite IH.
    now (destruct (f a)).
Qed.

Lemma filter_true:
  forall (A:Type) (p:A->bool)(l:list A),
    (forall a, In a l -> p a = true) -> 
    filter p l = l.
Proof.
  intros A p l Hin.
  induction l as [| x xs IH].
  - trivial.
  - simpl. rewrite Hin.
    + rewrite IH; trivial.
      intros a H. apply Hin.
      intuition.
    + intuition.
Qed.

Lemma filter_false:
  forall (A:Type) (p:A->bool)(l:list A),
    (forall a, In a l -> p a = false) -> 
    filter p l = nil.
Proof.
  intros A p l Hin.
  induction l as [| x xs IH].
  - trivial.
  - simpl. rewrite Hin.
    + rewrite IH; trivial.
      intros a H. apply Hin.
      intuition.
    + intuition.
Qed.

(** * Efficient compositions of [List.filter] and [List.map] *)

Fixpoint filter_map (A B :  Type) (select :  B -> bool) (f  : A -> B) l :=
  match l with
  | [ ]  => [ ]
  | a::l => let a' := f a in
           if (select a')
           then a'::filter_map select f l
           else filter_map select f l
  end.

Fixpoint map_filter (A B :  Type) (select :  A -> bool) (f  : A -> B) l :=
  match l with
  | [ ]  => [ ]
  | a::l => if (select a)
           then (f a)::map_filter select f l
           else map_filter select f l
  end.

Fixpoint filter_map_some A B (f:A->option B) l : list B :=
  match l with
  | [ ] => [ ]
  | h::t => match f h with
           | None => filter_map_some f t
           | Some b => b::(filter_map_some f t)
           end
  end.

(** * Properties of  [filter_map] and [map_filter] *)

Lemma filter_map_fusion:
  forall (A B :Type) (select :  A -> bool) (f  : B -> A) l,
    filter select (map f l) =  filter_map select f  l.
Proof.
  induction l as [ | a l IH ]; simpl.
  - trivial.
  - destruct (select (f a)).
    + now rewrite <- IH.
    + trivial.
Qed.

Lemma map_filter_fusion:
  forall (A B :Type) (select :  A -> bool) (f  : A -> B) l,
    map f (filter select l) =  map_filter select f  l.
Proof.
  induction l as [ | a l IH ]; simpl.
  - trivial.
  - destruct (select a).
    + now rewrite <- IH.
    + trivial.
Qed.

Hint Rewrite  filter_map_fusion map_filter_fusion : optimization.

Lemma filter_map_false:
  forall (A B:Type)(p:B->bool)(f:A->B)(l:list A),
    (forall (a:A), p(f a) = false) ->
    filter p (map f l) = nil.
Proof.
  intros A B p f l H.
  apply filter_false.
  intros a HIn.
  apply in_map_iff in HIn.
  destruct HIn as [a' [ Ha' HIn ]].
  rewrite <- Ha'.
  apply H.
Qed.

Definition is_some A (x:option A) : bool :=
  match x with
  | None => false
  | _ => true
  end.

Lemma filter_map_some_prop: 
  forall (A B :Type)(f: A->option B)(l:list A),
    map Some (filter_map_some f l) = filter (@is_some B) (map f l).
Proof.
  induction l; trivial.
  destruct (f a) as [ b | ] eqn:Hfa;
    simpl; rewrite Hfa; simpl; now rewrite IHl.
Qed.

Lemma filter_map_some_empty: 
  forall (A B :Type)(f: A->option B)(l:list A),
    (forall x, In x l -> f x = None) ->
    filter_map_some f l = [ ].
Proof.
  induction l; intros H; trivial; simpl.
  rewrite H by (simpl; auto).
  apply IHl.
  intros; apply H; simpl; auto.
Qed.
