Require Import Coq.Lists.List Program Relation_Definitions.
Import ListNotations.
Set Implicit Arguments.

(** * Functions on the [option] Type *)

(** Removing the [Some] constructor using a proof that the argument is
    different from [None]. *)          
Program Definition 
  no_some(A:Type)(a:option A| a <> None) : A :=
  match a with 
    | None => _ 
    | Some x => x
  end.

Lemma no_some_spec :
  forall (A:Type)(a:option A| a <> None),
    Some (no_some a) = `a.
Proof.
  intros A [[a| ] Ha]; unfold no_some; [auto | contradict Ha; trivial].
Qed.

(** Properties of [no_some] and [Some]. *)
Lemma some_no_some: 
  forall(A:Type)(a:option A)(H:a<>None),
    Some(no_some(exist _ a H)) = a.
Proof.
  intros A a Ha;
  destruct a; simpl; auto; elim Ha; auto.
Qed.

Lemma some_inj_eq: 
  forall(A:Type)(x y:A), x = y <-> Some x = Some y.
Proof.
  intros A x y; split;intro H; 
  [ f_equal | inversion H ]; auto.
Qed.

#[export] Hint Rewrite some_no_some: option.

(** Conversion to [bool]. *)
Definition is_some (A:Type)(x:option A) : bool := 
  match x with 
    | None => false 
    | Some _ => true
  end.

Lemma is_some_true_not_none:
  forall (A:Type)(x: option A), 
    is_some x = true -> x<>None.
Proof.
  destruct x; intro H; discriminate.
Qed.

(** [map_filter_some] applies a function [f:A->option B] to each
     element of a list. If [(f a)] is [None], the value is discarded,
     otherwise [no_some(f a)] is in the result list. *)
Fixpoint map_filter_some (A B :Type)(f: A->option B)(l:list A) := 
  match l with
    | nil => nil
    | cons h t => 
      match (f h) with 
	| Some x => x::map_filter_some f t
        | None => map_filter_some f t
      end
  end.

Lemma map_filter_some_prop: 
  forall (A B :Type)(f: A->option B)(l:list A),
    map Some (map_filter_some f l) = filter (@is_some B) (map f l).
Proof.
  induction l as [|x xs IH]; auto.
  case_eq (f x); [intros b Hfa | intros Hfa]; simpl;
  rewrite Hfa; simpl; f_equal; trivial.
Qed.

Lemma map_filter_some_ext :
  forall {A B} l (f f' : A -> option B), 
    (forall a:A, f a = f' a) ->
    map_filter_some f l =  map_filter_some f' l.
Proof.
  intros A0 B l f f'  H.
  induction l as [|x xs IH].
  - trivial.
  - simpl; rewrite H, IH; trivial.
Qed.
