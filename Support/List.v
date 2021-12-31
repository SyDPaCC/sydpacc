Require Import SyDPaCC.Support.Option.
Require Import Coq.Lists.List Coq.Classes.EquivDec Arith Lia.
Import ListNotations.

Generalizable All Variables.
Set Implicit Arguments.

(** * Additional Functions and Results on Lists *)

(** ** Hints and a tactic for [List.length] *)

#[export] Hint Rewrite map_length app_length seq_length combine_length : length.
 
Ltac length :=
  repeat (simpl; autorewrite with length; simpl; subst); auto with arith; try ring; try lia.

(** ** Association lists *)

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

(** ** Additional properties of [List.filter] *)

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

(** [filter_map_some] applies a function [f:A->option B] to each
     element of a list. If [(f a)] is [None], the value is discarded,
     otherwise [no_some(f a)] is in the result list. *)
Fixpoint filter_map_some A B (f:A->option B) l : list B :=
  match l with
  | [ ] => [ ]
  | h::t => match f h with
           | None => filter_map_some f t
           | Some b => b::(filter_map_some f t)
           end
  end.

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

#[export] Hint Rewrite  filter_map_fusion map_filter_fusion : optimization.

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

Lemma map_filter_some_ext :
  forall {A B} l (f f' : A -> option B), 
    (forall a:A, f a = f' a) ->
    filter_map_some f l =  filter_map_some f' l.
Proof.
  intros A0 B l f f'  H.
  induction l as [|x xs IH].
  - trivial.
  - simpl; rewrite H, IH; trivial.
Qed.

(** ** Additional lemmas on [List.map] and [List.flat_map] *)

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

Lemma flatmap_length:
  forall A B (f:A->list B)(xs:list A),
    length (flat_map f xs) =
    fold_left plus (map (@length B) (map f xs)) 0.
Proof.
  intros A B f; induction xs as [ | x xs IH]; auto.
  simpl; rewrite app_length, IH.
  clear IH; generalize dependent (length (f x)); induction xs as [ | y ys IH]; intro n.
  - auto with arith.
  - simpl. rewrite <- IH with (n:=n+length(f y)).
    rewrite <- IH.
    auto with arith.
Qed.

#[export] Hint Rewrite flatmap_length : length.

(** ** A terminal recursive version of [List.map]. *)

Fixpoint map_aux A B (f:A->B)(l:list A)(res:list B) : list B := 
  match l with 
    | [] => rev' res
    | x::xs => map_aux f xs ((f x)::res)
  end.

Definition map'  A B (f:A->B)(l:list A) : list B := map_aux f l [].

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

(** ** A boolean membership function on lists *)

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
  induction l as [ | a' l]; simpl in *.
    elim H.
    destruct H.
      rewrite H; case_eq(eqA a a); intros H'; 
        auto; elim H'; apply eq_refl.
      rewrite IHl; case_eq(eqA a' a); auto. 
  (* <- *)
  induction l as [ | a' l]; simpl in *.
    discriminate.
    destruct(eqA a' a); intuition.
Qed.

(** ** Additional results about [NoDup] *)

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

(** ** Additional Results about [List.combine] *)

Lemma combine_length':
  forall {A B: Type}{l:list A}{l':list B}(H:length l=length l'),
    length(combine l l') = length l.
Proof.
  intros A B l l' H.
  autorewrite with length. rewrite H.
  auto with arith.
  Qed.

Lemma combine_length'':
  forall {A B: Type}{l:list A}{l':list B}(H:length l=length l'),
    length(combine l l') = length l'.
Proof.
  intros A B l l' H.
  autorewrite with length. rewrite H.
  auto with arith.
Qed.

Lemma combine_app:
  forall A B (l1 l2:list A)(l1' l2':list B),
    length l1 = length l1' ->
    combine(l1++l2)(l1'++l2') =
    combine l1 l1' ++ combine l2 l2'.
Proof.
  intros A B; induction l1 as [ | h1 t1 IH]; intros l2 l1' l2' H; destruct l1' as [ | h1' t1' ]; simpl.
  - trivial.
  - simpl in H; discriminate.
  - simpl in H; discriminate.
  - simpl in H; inversion H as [ H' ]; subst; clear H.
    now rewrite IH.
Qed.

(** ** Additional results about [List.app] *)

Lemma list_last_app:
  forall A (xs:list A) x d,
    List.last (xs++[x]) d = x.
Proof.
  intros A; induction xs; intros x d.
  - now compute.
  - simpl; destruct(xs ++ [x]) eqn:H; symmetry in H.
    + apply app_cons_not_nil in H; now exfalso.
    + destruct xs; inversion H; subst; auto.
      rewrite app_comm_cons; apply IHxs.
Qed.

(** ** Additional results about [List.seq] *)

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
