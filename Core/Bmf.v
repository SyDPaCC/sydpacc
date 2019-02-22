Require Import Coq.Lists.List Program. Import ListNotations.
Set Implicit Arguments.
Generalizable All Variables.

(*-----------------------------------------------------------------*)

(** * Tupling, pairing, compose *)

Definition tupling A B C (f:A->B)(g:A->C) := fun x => (f x, g x).

Definition pairing A B C D (f:A->B)(g:C->D) :=
  fun (pair:A*C) => (f (fst pair), g (snd pair)).

Definition compose A B C (g : B -> C) (f : A -> B) : A->C :=
  fun x => g (f x).

Infix "△" := tupling (at level 41, left associativity) : sydpacc_scope.

Infix "×" := pairing (at level 41, left associativity) : sydpacc_scope.

Infix "∘" := compose (at level 40, left associativity) : sydpacc_scope.

Hint Unfold compose pairing tupling id. 

Open Scope sydpacc_scope.

(** * Algebraic Properties Defined as Coq Typeclasses *)

(** ** Unit *)
Class LeftNeutral A B (op: B -> A -> A) (e : B) :=
  {
    left_neutral  : forall a, op e a = a
  }. 

Class RightNeutral A B (op: A -> B -> A) (e : B) :=
  {
    right_neutral : forall a, op a e =  a
  }.

Class Neutral A (op: A -> A -> A) (e : A) :=
  {
    neutral_left_neutral  :>  LeftNeutral  op e;
    neutral_right_neutral :>  RightNeutral op e
  }. 

Program Instance app_neutral (A:Type) : Neutral (@List.app A) [].
Next Obligation. constructor. apply app_nil_l. Qed.
Next Obligation. constructor. apply app_nil_r. Qed.

(** ** Associativity  *)
Class  Associative A (op:A->A->A) :=
  {
    associative : forall (x y z: A), op (op x y) z = op x (op y z)
  }.

Instance app_assoc (A:Type) : Associative (@List.app A).
Proof.
  constructor. intros.
  now rewrite app_assoc.
Qed.

(** ** Commutativity  *)
Class Commutative A (op:A->A->A) :=
  {
    commutative : forall (x y: A), op  x y = op y x
  }.

(** ** Monoid *)
Class Monoid A (op : A->A->A) (e : A) := 
  {
    monoid_assoc   :> Associative op; 
    monoid_neutral :> Neutral op e
  }.

(** ** Distributivity *)
Class Distributivity  A (otimes:A->A->A) (oplus:A->A->A) :=
  {
    left_distributivity :
      forall x y z,
        otimes x (oplus y z) =  oplus (otimes x y) (otimes x z);

    right_distributivity :
      forall x y z, 
        otimes (oplus y z) x = oplus (otimes y x) (otimes z x)
  }.


(** ** Properties of Folds *)
Unset Implicit Arguments.
Lemma fold_left_prop A (f:A->A->A) {H:Associative f} :
  forall l (a b:A), fold_left f l (f a b) = f a (fold_left f l b).
Proof.
  induction l as [ | x xs IH ].
  - intros. trivial.
  - intros a b. simpl.
    repeat rewrite IH.
    now rewrite <- (associative a).
Qed.

Lemma fold_right_prop A (f:A->A->A) {H:Associative f} : 
  forall l a b, fold_right f (f a b) l = f (fold_right f a l) b.
Proof.
  induction l as [ | x xs IH ].
  - trivial.
  - intros a b. simpl.
    rewrite IH.
    now rewrite associative.
Qed.
Set Implicit Arguments.

Lemma fold_left_map_r:
  forall A B C (f:A->B->A) (g :C->B) (l:list C) (a:A),
    fold_left (fun a b => f a (g b)) l a = fold_left f (map g l) a.
Proof.
  induction l as [ | a l IHl]; intro.
  - reflexivity.
  - simpl; rewrite IHl; reflexivity.
Qed.

Lemma fold_right_map_l:
  forall A B C (f:B->A->A) (g:C->B) (l:list C) (a:A),
    fold_right (fun a b => f (g a) b) a l = fold_right f a (map g l).
Proof.
  induction l as [ | a l IHl]; intros.
  - reflexivity.
  - simpl.  f_equal; rewrite IHl; reflexivity.
Qed.


(** * Induction on Lists Seen as Join-Lists *)

(** A Join-List is either:
    - an empty list,
    - a singleton list,
    - the concatenation of two lists.
    the empty list and concatenation form a monoid. *)

Lemma joinlist_induction :
  forall A, forall P : list A -> Prop, 
      (P nil) ->
      (forall a, P [a]) ->
      (forall x y , P x -> P y -> P (x++y)) ->
      forall l,  P l.
Proof.
  intros A P Hnil Hsingleton Hconcat l.
  induction l as [ | a x IH ].
  - trivial.
  - replace (a::x) with ([a]++x) by reflexivity.
    now apply Hconcat.
Qed.

Unset Implicit Arguments.

(** * Reduce on Arbitrary Lists and Properties *)
Definition reduce  `(op:A -> A -> A) `{m: Monoid A op e} := 
  fun l => fold_left op l e.
Set Implicit Arguments.

Lemma reduce_app:
  forall A (op:A->A->A)`{m: Monoid A op e} (l1 l2:list A),
    reduce op (l1 ++ l2) = op (reduce op l1) (reduce op l2).
Proof.
  intros A op e m l1 l2. unfold reduce.
  now rewrite fold_left_app, <- fold_left_prop, right_neutral
    by typeclasses eauto.
Qed.

(*-----------------------------------------------------------------*)

(** * Homomorphic Functions and List Homomorphisms *)

Class Homomorphic `(h:list A->B) `(op:B->B->B) := 
  { homomorphic : forall x y, h (x++y) = op (h x) (h y) }.  

(** ** Image of a List Function  *)

Definition img `(h:list A->B) := { b:B | exists l, h l = b }.

(*-----------------------------------------------------------------*)

(** ** [h] homomorphic -> homomophism on the image of [h] *)

Definition to_img A B (h:list A->B)(xs:list A) : img h.
  exists(h xs).
  now eexists.
Defined.

Definition of_img `{h:list A->B}(x:img h) : B :=
  proj1_sig x. 

Lemma to_img_prop : 
  forall A B {h:list A->B}(xs ys:list A),
    xs = ys -> to_img h xs = to_img h ys.
Proof.
  intros A B h xs ys Heq.
  rewrite Heq.
  reflexivity.
Qed.

Lemma norm : 
  forall A B {h:list A->B}(b:img h), exists xs, b = to_img h xs.
Proof.
  intros A B h b.
  destruct b as [b [xs Hb]].
  exists xs.
  rewrite <- Hb.
  now apply to_img_prop.
Qed.

Lemma img_op:
  forall A B (h:list A->B)(op:B->B->B)
         (hom:Homomorphic h op)(b1 b2:B),
    (exists xs1, h xs1 = b1) -> 
    (exists xs2, h xs2 = b2) -> 
    (exists xs, h xs = op b1 b2).
Proof.
  intros A B h op hom b1 b2 
         [xs1 Hb1] [xs2 Hb2].
  rewrite <- Hb1, <- Hb2, <- homomorphic.
  exists (xs1++xs2). 
  reflexivity.
Defined.


Unset Implicit Arguments.
Program Definition restrict_op `(op:B->B->B) `{Homomorphic A B h op} : 
  img h -> img h -> img h := op.
Next Obligation.
  destruct x as [x [lx Hx]]; destruct x0 as [y [ly Hy]].
  apply img_op.
  - trivial.
  - eexists; eassumption.
  - eexists; eassumption.
Defined.
Set Implicit Arguments.

Program Definition restrict `{Homomorphic A B h op} 
        `(Eq: forall a b : img h,  op' a b = proj1_sig (restrict_op op a b) ) : 
  img h -> img h -> img h := op'.
Next Obligation.
  destruct x as [x [lx Hx]]; destruct x0 as [y [ly Hy]].
  rewrite Eq; simpl; apply img_op.
  - trivial.
  - eexists; eassumption.
  - eexists; eassumption.
Defined.

Lemma restrict_to_img:
  forall `{hom:Homomorphic A B h op}
         `(Eq: forall a b : img h, op' a b = proj1_sig(restrict_op op a b)) 
         (xs ys:list A),
    restrict Eq (to_img h xs)(to_img h ys) =
    to_img h (xs++ys).
Proof.
  intros A B h op hom op' Eq xs ys.
  unfold restrict, restrict_obligation_1, to_img; simpl.
  destruct hom as [hom].
  rewrite Eq; simpl; rewrite <- hom.
  reflexivity.
Qed.

Program Instance homomorphic_restrict_assoc `{Homomorphic A B h op}
        `(Eq: forall a b : img h, op' a b = proj1_sig(restrict_op op a b)) : 
  Associative (restrict Eq).
Next Obligation.
  destruct (norm x) as [xs1 Hb1].
  destruct (norm y) as [xs2 Hb2].
  destruct (norm z) as [xs3 Hb3].
  subst.
  repeat rewrite restrict_to_img.
  apply to_img_prop.
  now rewrite associative.
Qed.

Program Instance homomorphic_restrict_neutral `{Homomorphic A B h op}  
        `(Eq: forall a b : img h, op' a b = proj1_sig(restrict_op op a b)) : 
  Neutral (restrict Eq) (to_img h []).
Next Obligation.
  constructor; intro x.
  destruct (norm x) as [xs Hx]; subst.
  rewrite restrict_to_img; now apply to_img_prop.
Qed.
Next Obligation.
  constructor; intro x.
  destruct (norm x) as [xs Hx]; subst.
  rewrite restrict_to_img.
  apply to_img_prop.
  apply app_nil_r.
Qed.

Program Instance homomorphic_restrict_monoid `{Homomorphic A B h op} 
        `(Eq: forall a b : img h, op' a b = ` (restrict_op op a b)) : 
  Monoid (A:=(img h)) (restrict Eq) (h []).

(** ** Optimization of Homomophisms *)

Unset Implicit Arguments.
Class Optimised_f `(h:list A->B)`{H:Homomorphic A B h op} :=
  {
    optimised_f_sig: { f: A->B | forall a, f a = h[a] }
  }.

Class Optimised_op `(h:list A->B)`{H:Homomorphic A B h op} :=
  {
    optimised_op_sig: {op':(img h)->(img h)->B|forall a b, op' a b = op (` a) (` b) }
  }.

Program Definition optimised_f `(h:list A->B) `{Ho:Optimised_f A B h} : A -> img h :=
  optimised_f_sig (h:=h).
Next Obligation.
  rewrite (proj2_sig optimised_f_sig).
  now eexists.
Defined.

Definition optimised_op `(h:list A->B)`{H:Optimised_op A B h}: img h -> img h -> img h.
  intros a b.
  apply (exist _ ((` optimised_op_sig) a b)).
  destruct a as [a [la Ha]], b as [b [lb Hb]].
  rewrite (proj2_sig optimised_op_sig); simpl.
  rewrite <- Ha, <- Hb, <- homomorphic.
  now eexists.
Defined.
Set Implicit Arguments.

Instance non_optimised_f `{Homomorphic A B h op} : Optimised_f h.
Proof. constructor. eexists. reflexivity. Qed.

Instance non_optimised_op `{Homomorphic A B h op} : Optimised_op h.
Proof. constructor. eexists. reflexivity. Qed.

(*-----------------------------------------------------------------*)

(** ** Homomophism Theorems *)

Unset Implicit Arguments.
Definition hom_to_map_reduce {A B:Type}(h:list A->B)
           `{H:Homomorphic A B h op}
           `{@Optimised_op A B h op H}`{@Optimised_f A B h op H} :
  list A -> img h := 
  (reduce (optimised_op h)) ∘ (List.map (optimised_f h)).
Set Implicit Arguments.

(** *** First Homomophism Theorem *)

Theorem first_homomorphism_theorem:
  forall `{H:Homomorphic A B h op}`{@Optimised_op A B h op H}`{@Optimised_f A B h op H},
  forall l, h l = of_img (hom_to_map_reduce h l).
Proof.
  unfold hom_to_map_reduce.
  intros A B h op hom opt_op opt_f l; induction l as [ | x xs IH ].
  - reflexivity.
  - unfold compose, of_img, Basics.compose in *; simpl in *.
    replace (optimised_f h x :: map (optimised_f h) xs)
    with ([optimised_f h x] ++ map (optimised_f h) xs) by trivial.
    rewrite reduce_app ; simpl.
    rewrite (proj2_sig optimised_op_sig), <- IH; simpl.
    rewrite (proj2_sig optimised_op_sig); simpl.
    rewrite (proj2_sig optimised_f_sig); simpl.
    now repeat rewrite <- homomorphic.
Qed. 

Class Rightwards `(h:list A->B)`(op:B->A->B)`(e:B) := 
  { rightwards: forall l, h l = List.fold_left op l e }.

Class Leftwards `(h:list A->B)`(op:A->B->B)`(e:B) := 
  { leftwards: forall l, h l = List.fold_right op e l }.

(** *** Third Homomophism Theorem *)

Class Right_inverse `(h:list A ->B)(h':B->list A) :=
  { right_inverse: forall l, h l = h(h'(h l)) }.

Lemma hom_characterisation:
  forall `(h:list A->B)`{Right_inverse A B h h'},
    (exists op, forall x y, h (x++y) = op (h x) (h y)) <->
    (forall x y v w, h x = h v -> h y = h w -> h(x ++ y) = h(v ++ w)).
Proof.
  intros A B h h' Hinv. split; intro H.
  - intros x y v w Hxv Hyw.
    destruct H as [op Hh].
    repeat rewrite Hh.
    rewrite Hxv, Hyw.
    trivial.
  - exists(fun l r=>h((h' l)++(h' r))).
    intros x y.
    erewrite H; try reflexivity; apply right_inverse.
Qed.

Global Instance third_homomorphism_theorem_right_inverse
         `{h:list A->B}`{inv:Right_inverse A B h h'}
         `{Hl:Leftwards A B h opl e} `{Hr:Rightwards A B h opr e} : 
  Homomorphic h (fun l r =>h( (h' l)++(h' r))).
Proof.
  constructor; intros x y.
  assert(exists op, forall x y, h (x++y) = op (h x) (h y)) as Hom.
  { 
    eapply hom_characterisation; try eassumption.
    intros x0 y0 v w H0 H1.
    rewrite leftwards.
    rewrite fold_right_app.
    rewrite <- (leftwards y0), H1. rewrite (@leftwards _ _ _ _ _ Hl).
    rewrite <- fold_right_app.
    rewrite <- leftwards.
    rewrite rightwards.
    rewrite fold_left_app.
    rewrite <-(rightwards x0), H0, (@rightwards _ _ _ _ _ Hr).
    rewrite <- fold_left_app.
    rewrite <- rightwards.
    trivial.
  }
  destruct Hom as [op Hh].
  repeat rewrite Hh.
  repeat rewrite <- right_inverse.
  trivial.
Qed.

(** * A Typeclass to Characterize Empty Lists *)

Class NonEmpty `(l:list A) := { non_emptiness : l<> [] }.

(*---------------------------------------------------------------*)

Ltac empty := 
  let H := fresh "Hempty" in 
  assert(H:=non_emptiness); contradict H; trivial.

(** ** Instances *)

Program Instance cons_non_empty 
        `(x:A)(xs:list A) : NonEmpty (x::xs).

Program Instance map_non_empty 
        `(f:A->B)(xs:list A){HNE:NonEmpty xs} : 
  NonEmpty (map f xs).
Next Obligation.
  destruct xs.
  - empty.
  - intro H. discriminate.
Qed.

Lemma eq_non_empty :
  forall {A:Type}{l1 l2:list A}{HNE:NonEmpty l1}(Eq:l1=l2), NonEmpty l2.
Proof. 
  constructor; intro H; subst; destruct HNE as [HNE]; now contradict HNE.
Qed.

Instance app_non_empty_l 
         {A:Type}(l1 l2:list A){HNE:NonEmpty l1} : NonEmpty (l1++l2).
Proof.
  constructor; destruct HNE as [HNE]; contradict HNE.
  now apply app_eq_nil in HNE.
Qed.

Instance app_non_empty_r 
         {A:Type}(l1 l2:list A){HNE:NonEmpty l2} : NonEmpty (l1++l2).
Proof.
  constructor; destruct HNE as [HNE]; contradict HNE.
  now apply app_eq_nil in HNE.
Qed.

Lemma non_empty_cons `{NonEmpty A xs} : 
  exists x' xs', xs = x' :: xs'.
Proof.
  destruct xs as [ | x' xs'].
  - empty. 
  - exists x'. now exists xs'.
Qed.

(*---------------------------------------------------------------*)

(** ** Reduce on Non-empty Lists and Properties *)

Module NE.

  Unset Implicit Arguments.
  Definition reduce `(op:A->A->A)`{HA:Associative A op}
             (l:list A){HNE:NonEmpty l} : A.
    destruct l as [|x xs].
    - apply False_rect. now apply HNE.
    - exact(fold_left op xs x).
  Defined.
  
  Lemma reduce_app:
    forall `(op:A->A->A)`{HA:Associative A op}
           (l1 l2:list A){HNE1:NonEmpty l1}{HNE1:NonEmpty l2},
      reduce op (l1++l2) = op (reduce op l1) (reduce op l2).
  Proof.
    intros A op Hassoc; induction l1; intros l2 HNE1 HNE2.
    - inversion HNE1; intuition.
    - destruct l2; simpl.
      + inversion HNE2; intuition.
      + rewrite fold_left_app. simpl.
        now rewrite fold_left_prop.
  Qed.
  
  Lemma reduce_pi:
    forall `(op:A->A->A)`{HA:Associative A op}
           (l1 l2:list A){HNE:NonEmpty l1}{HNE:NonEmpty l2}(H:l1=l2),
      reduce op l1 = reduce op l2.
  Proof.
    intros A op Hassoc; induction l1; intros l2 HNE1 HNE2 H.
    - inversion HNE1; intuition.
    - destruct l2; inversion HNE2; intuition.
      now inversion H; subst.
  Qed.      

  Lemma reduce_fold_left:
    forall `(op:A->A->A)`{HA:Associative A op} x xs,
      reduce op (x::xs) = fold_left op xs x.
    induction xs; trivial.
  Qed.
  Set Implicit Arguments.
  
End NE.

(*-------------------------------------------------------------*)

(** ** Compositions Taking into Account Non-emptyness *)

Program Definition comp' 
        `(f:forall l:list B, NonEmpty l->C)`(g:list A->list B)
        {HNE:forall a, NonEmpty a -> NonEmpty(g a)} : 
  forall l:list A, NonEmpty l -> C := 
  fun a H => f (g a) (HNE a H).

Program Definition comp'' 
        `(f:forall l:list B, NonEmpty l->C)`(g:A->list B)
        {HNE:forall a, NonEmpty(g a)} : A -> C := 
  fun a => f (g a) (HNE a).

Infix "∘'" := comp' (at level 30).
Infix "∘''" := comp'' (at level 30).

(*---------------------------------------------------------------*)

(** * Prefixes of a Lists and its Properties *)
Fixpoint prefix `(xs:list A) := 
  match xs with 
    | [] => [[]]
    | x::xs => []::(map (cons x) (prefix xs))
  end.

Example prefix_informal : 
  prefix ([1;2;3])%nat =  ([[]; [1]; [1; 2]; [1; 2; 3]])%nat. 
Proof. trivial. Qed.

Instance prefix_non_empty `(xs:list A) : NonEmpty (prefix xs).
Proof.
  constructor; intro H; destruct xs; simpl; discriminate.
Qed.

Lemma prefix_snoc (A:Type) : 
  forall (xs:list A)(x:A),
    prefix (xs++[x]) = prefix xs ++ (map (app xs) [[x]]).
Proof.
  induction xs as [ | x' xs' IH].
  - trivial.
  - intro x. simpl. 
    now rewrite IH, map_app.
Qed.

Lemma prefix_app (A:Type) :
  forall (l l':list A), 
    prefix (l ++ l') = prefix l ++ tl(map (app l) (prefix l')).
Proof.
  intros l l'; revert l.
  induction l'.
  - intros l'. simpl; repeat rewrite app_nil_r. trivial.
  - intros l.
    change ( a :: l') with ([a]++l').
    rewrite <- associative.
    rewrite IHl', prefix_snoc, IHl', map_app.
    simpl.
    rewrite associative.
    assert(NonEmpty (prefix l')) by typeclasses eauto.
    destruct non_empty_cons as [x' [xs' Heq]].
    repeat rewrite Heq. simpl.
    rewrite map_map.
    do 2 f_equal. apply map_ext.
    intros. now rewrite associative.
Qed.

Lemma prefix_last:
  forall `(l:list A) {H: NonEmpty l}, prefix l = prefix (removelast l) ++ [l].
Proof.
  induction l as [ | x xs IH] using rev_ind; intro HnonEmpty.
  - empty.
  - rewrite prefix_snoc.
    destruct xs as [ | x' xs] using rev_ind.
    + trivial.
    + rewrite removelast_app by (intro H; discriminate).
      now rewrite app_nil_r.
Qed.  

Lemma prefix_length (A:Type) :  
  forall (l:list A), length (prefix l) = Datatypes.S (length l).
Proof.
  induction l; simpl; try rewrite map_length; now f_equal.
Qed.

Hint Rewrite prefix_length : length.

Close Scope sydpacc_scope.