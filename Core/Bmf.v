Require Import Coq.Lists.List Program Arith NArith Lia.
Import ListNotations.
Require Import SyDPaCC.Support.NList SyDPaCC.Support.List.
Set Implicit Arguments.
Generalizable All Variables.

(** * Tupling, pairing, compose *)

Definition id {A} (x:A) := x.

Definition tupling A B C (f:A->B)(g:A->C) := fun x => (f x, g x).

Definition pairing A B C D (f:A->B)(g:C->D) :=
  fun (pair:A*C) => (f (fst pair), g (snd pair)).

Definition compose A B C (g : B -> C) (f : A -> B) : A->C :=
  fun x => g (f x).

Declare Scope sydpacc_scope.

Infix "△" := tupling (at level 41, left associativity) : sydpacc_scope.

Infix "×" := pairing (at level 41, left associativity) : sydpacc_scope.

Global Infix "∘" := compose (at level 40, left associativity) : sydpacc_scope.

#[export] Hint Unfold compose pairing tupling id : sydpacc.

Open Scope sydpacc_scope.

(*-----------------------------------------------------------------*)

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

(*-----------------------------------------------------------------*)

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

(** ** Associativity  *)
Class  Associative A (op:A->A->A) :=
  {
    associative : forall (x y z: A), op (op x y) z = op x (op y z)
  }.

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

(** ** Instances *)

#[export] Instance app_associative (A:Type) : Associative (@List.app A).
Proof.
  constructor. intros.
  now rewrite app_assoc.
Qed.

#[export] Instance app_neutral (A:Type) : Neutral (@List.app A) [].
  repeat constructor; apply app_nil_r.
Qed.

#[export] Instance plus_neutral (A:Type) : Neutral plus 0.
  repeat constructor; auto with arith.
Qed.

#[export] Instance plus_associative : Associative plus.
  constructor; auto with arith.
Qed.

#[export] Instance andb_monoid: Monoid andb true.
Proof.
  repeat constructor.
  - intros; now rewrite Bool.andb_assoc.
  - intros; now rewrite Bool.andb_true_r.
Qed.


(*-----------------------------------------------------------------*)

(** * Optimization of Arbitrary Functions *)

Class Opt A B (f g:A->B) :=
  {
    opt_eq: forall a, f a = g a
  }.

Class Opt2 A B C (f g:A->B->C) :=
  {
    opt2_eq: forall a b, f a b = g a b
  }.

(*-----------------------------------------------------------------*)

(** * Properties of Folds *)

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

(** * [fold_left2] and Properties *)

Fixpoint fold_left2 A B C (op:C->A*B->C) (e:C) (l1:list A) (l2:list B): C :=
  match (l1, l2) with
  | ([], _ ) | (_ , []) => e
  | (h1::t1, h2::t2) =>
    fold_left2 op (op e (h1,h2)) t1 t2
  end.

Lemma fold_left2_prop1:
  forall A B C (op:C->A*B->C) e l1 l2,
    fold_left op (combine l1 l2) e = fold_left2 op e l1 l2.
Proof.
  intros A B C op e l1 l2; revert e l2;
    induction l1 as [ | h1 t1 IH1]; intros e l2; destruct l2 as [ | h2 t2 ].
  - trivial.
  - trivial.
  - trivial.
    - simpl; now rewrite IH1.
Qed.

Lemma fold_left2_prop2:
  forall A A' B C op (f:A*B->A') (e:C) l1 l2,
    fold_left op (map f (combine l1 l2)) e = fold_left2 (fun u p =>op u (f p))  e l1 l2.
Proof.
  intros A A' B C op f e l1 l2; revert e l2;
    induction l1 as [ | h1 t1 IH1]; intros e l2; destruct l2 as [ | h2 t2 ]; trivial.
  simpl; now rewrite IH1.
Qed.

(*-------------------------------------------------------------*)

(** * Prefixes of a Lists and its Properties *)

Fixpoint prefix `(xs:list A) := 
  match xs with 
    | [] => [[]]
    | x::xs => []::(map (cons x) (prefix xs))
  end.

Example prefix_informal : 
  prefix ([1;2;3])%nat =  ([[]; [1]; [1; 2]; [1; 2; 3]])%nat. 
Proof. trivial. Qed.

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
    rewrite app_assoc.
    rewrite IHl', prefix_snoc, IHl', map_app.
    simpl.
    rewrite <- app_assoc.
    destruct(prefix l') eqn:Heq.
    + trivial.
    + simpl; rewrite map_map.
    do 2 f_equal. apply map_ext.
    intros. now rewrite <- app_assoc.
Qed.  

Lemma prefix_map:
  forall A B (f:A->B) xs,
    prefix(map f xs) = map (map f)(prefix xs).
Proof.
  intros A B f; induction xs as [ | x xs IH].
  - trivial.
  - simpl; now rewrite IH, map_map, map_map.
Qed.

Lemma prefix_length (A:Type) :  
  forall (l:list A), List.length (prefix l) = S (List.length l).
Proof.
  induction l; simpl; try rewrite List.map_length; now f_equal.
Qed.

Lemma prefix_contains_nil :
  forall `(l:list A), exists l', prefix l = [] :: l'.
Proof.
  induction l as [ | h t IH ].
  - now eexists.
  - inversion IH. simpl. eexists. f_equal.
Qed.        

#[export] Hint Rewrite prefix_length : length.

(*-----------------------------------------------------------------*)

(** * Definition and Properties of Prefix Sum Computations *)

Fixpoint scanl A B (op:A->B->A)(e:A)(l:list B) : list A := 
  e::match l with 
     | []   => []
     | h::t => scanl op (op e h) t
     end.

Example scanl_example  : scanl plus 0 [1;2;3] = [0; 0+1 ; 0+1+2 ; 0+1+2+3].
Proof. reflexivity. Qed.

Lemma scanl_spec:
  forall A B (op:A->B->A) (e:A) (l : list B),
  scanl op e l =
  map (fun l => fold_left op l e) (prefix l).
Proof.
  intros A B op e l; revert op e ; induction l as [ | h t IH].
  - trivial.
  - intros op e; simpl.
    now rewrite IH, map_map.
Qed.

Lemma scanl_snoc:
  forall A B (op:A->B->A) (e:A) (l : list B) (b:B),
    scanl op e (l ++ [ b ]) = scanl op e l ++ [ fold_left op (l++[b]) e ].
Proof.
  intros A B op e l; revert e; induction l as [ | h t IH]; intros e b.
  - trivial.
  - simpl. now rewrite IH.
Qed.
  
Fact scanl_cons:
  forall A B (op:A->B->A) (e:A) (l : list B),
    scanl op e l = e::tl(scanl op e l).
Proof.
  intros A B op e l; destruct l; auto.
Qed.

Lemma scanl_map_gen:
  forall A B `{Monoid A op}(xs:list B) (q:B->A) c,
    scanl (fun s t=>op s (q t)) c xs = map (op c)(scanl (fun s t=>op s (q t)) e xs).
Proof.
  intros A B op e H xs q c; revert e c H.
  induction xs as [ | x' xs' IH ]; intros e c H.
  - simpl; now rewrite right_neutral.
  - simpl. 
    rewrite IH with (e:=e) by typeclasses eauto.
    rewrite @right_neutral with (e:=e) by typeclasses eauto.
    rewrite @left_neutral with (a:=q x') (e:=e) by typeclasses eauto.
    rewrite IH with (c:=q x')(e:=e) by typeclasses eauto.
    rewrite map_map.
    f_equal; apply map_ext; intro; now rewrite associative.
Qed.

Lemma scanl_map:
  forall `{Associative A op} e (x:A)(xs:list A),
    scanl op (op x e) xs = map (op x)(scanl op e xs).
  intros A op H e x xs. revert e x. induction xs as [ | x' xs' IH ].
  - intros; simpl; do 2 f_equal.
  - intros e x; simpl. f_equal.
    rewrite <- IH. f_equal.
    now rewrite associative.
Qed.

Lemma map_scanl:
  forall A B `{Monoid A op}(q:B->A) a c,
    scanl op c (map q a) =
    scanl (fun (s : A) (t : B) => op s (q t)) c a.
Proof.
  intros A B op e H q a c.
  repeat rewrite scanl_spec.
  rewrite prefix_map, map_map.
  apply map_ext; intro x.
  symmetry. apply fold_left_map_r.
Qed.
  
Lemma scanl_length:
  forall (A B:Type)(op:A->B->A)(identity:A)(l:list B),
    List.length (scanl op identity l) = S (List.length l).
Proof.  
  intros A B op identity l; generalize dependent identity; induction l as [ | h t IHl]; intros.
  - trivial.
  - simpl; now rewrite IHl.
Qed.

#[export] Hint Rewrite scanl_length : length.

Fixpoint scanl_aux A B (op:A->B->A)(e:A)(l:list B)(res:list A) : list A :=
  match l with
  | [] => rev' (e::res)
  | h::t => scanl_aux op (op e h) t (e::res)
  end.

Definition scanl' A B (op:A->B->A)(e:A)(l:list B) : list A :=
  scanl_aux op e l [].

#[export] Hint Unfold scanl' : sydpacc.

Fact scanl_aux_scanl:
  forall A B (op:A->B->A) e l l',
    scanl_aux op e l l' =
    rev' l' ++ scanl op e l.
Proof.
  intros A B op e l l'; revert e l';
    induction l as [ | h t IH ]; intros e l'.
  - simpl. unfold rev'. simpl.
    rewrite rev_append_rev.
    now rewrite rev_alt.
  - simpl; rewrite IH.
    unfold rev'; simpl.
    rewrite rev_append_rev.
    now rewrite rev_alt, <- List.app_assoc.
Qed.
 
Lemma scanl_scanl':
  forall A B (op:A->B->A) e l,
    scanl op e l = scanl' op e l.
Proof.
  intros A B op e l; revert e; induction l as [ | h t IH ]; intro e.
  - trivial.
  - autounfold with sydpacc. simpl.
    now rewrite scanl_aux_scanl.
Qed.

Unset Implicit Arguments.

Definition scan A (op:A->A->A) `{Monoid A op e} (l : list A):= scanl op e l.

Arguments scan [A] op {e} {_}.

Set Implicit Arguments.

#[export] Hint Unfold scan : sydpacc.

Fact scan_spec:
  forall A `(Monoid A op e) (l : list A),
  scan op l =
  map (fun l => fold_left op l e) (prefix l).
Proof.
  autounfold; intros; apply scanl_spec.
Qed.  

Lemma scan_length:
  forall (A B : Type)`(Monoid A op e)(l:list A),
    List.length (scan op l) = S(List.length l).
Proof.
  autounfold; intros; apply scanl_length.
Qed.

#[export] Hint Rewrite scan_length : length.

Lemma scan_map:
  forall  `{Monoid A op e} (x:A)(xs:list A),
    scan op (x::xs) = e::(map (op x) (scan op xs)).
Proof.
  intros A op e H x xs.
  autounfold with sydpacc; simpl. 
  rewrite <- scanl_map.
  do 2 f_equal.
  now rewrite left_neutral, right_neutral.
Qed.

Fixpoint scanl_last A B (op:A->B->A)(e:A)(l:list B) : list A * A := 
  match l with 
    | []   => ([], e)
    | h::t =>
      let result := scanl_last op (op e h) t in
      (e::fst result, snd result)
  end.

Fixpoint scanl_last_aux A B (op:A->B->A)(e:A)(l:list B) acc_l : list A * A := 
  match l with
  | [] => (List.rev' acc_l, e)
  | h::t => scanl_last_aux op (op e h) t (e::acc_l)
  end.

Definition scanl_last' A B (op:A->B->A)(e:A)(l:list B) : list A * A :=
  scanl_last_aux op e l [].

Lemma scanl_last_scanl_last_aux:
  forall A B (l:list B)(op:A->B->A)(e:A) acc,
    ((List.rev' acc)++(fst(scanl_last op e l)), snd(scanl_last op e l)) =
    scanl_last_aux op e l acc.
Proof.
  induction l as [ | h t IH]; intros op e acc.
  - simpl; f_equal; now rewrite right_neutral.
  - simpl; rewrite <- IH; unfold rev'; rewrite List.rev_append_rev; simpl;
      rewrite List.rev_append_rev; f_equal.
    now repeat rewrite associative.
Qed.

Lemma scanl_last_scanl_last':
  forall A B (l:list B)(op:A->B->A)(e:A),
    scanl_last op e l = scanl_last' op e l.
Proof.
  intros A B l op e; unfold scanl_last'.
  rewrite <- scanl_last_scanl_last_aux; simpl.
  apply surjective_pairing.
Qed.
    
Lemma scanl_last_fst_scanl:
  forall (A B:Type)(op:A->B->A)(e:A)(l:list B),
    fst (scanl_last op e l) = removelast (scanl op e l).
Proof.
  intros A B op e l; revert e; induction l as [|x xs IH].
  - trivial.
  - intro e; simpl; rewrite IH.
    destruct(scanl op (op e x) xs) eqn:H.
    + assert (List.length(scanl op (op e x) xs) = S (List.length xs)) as Hlen
          by apply scanl_length.
      rewrite H in Hlen; simpl in Hlen; discriminate.
    + trivial.
Qed.

Lemma scanl_scanl_last:
  forall (A B:Type)(op:A->B->A)(e:A)(l:list B),
    scanl op e l = (fst (scanl_last op e l))++[snd(scanl_last op e l)].
Proof.
  intros A B op e l; revert e; induction l as [|x xs IH]; intro e.
  - trivial.
  - simpl; f_equal; now rewrite IH.
Qed.

Lemma scanl_last_snd:
  forall (A B:Type)(op:A->B->A)(e:A)(l:list B),
    snd (scanl_last op e l) = List.fold_left op l e.
Proof.
  intros A B op e l; revert e; induction l as [|x xs IH].
  - trivial.
  - intro e; simpl; rewrite IH; trivial.
Qed.

Lemma list_last_scanl:
  forall A B (op:A->B->A) e xs d,
    last(scanl op e xs) d = snd(scanl_last op e xs).
Proof.
  intros A B op e xs d.
  transitivity (last(fst (scanl_last op e xs)++[snd(scanl_last op e xs)]) d).
  - now rewrite scanl_scanl_last.
  - apply list_last_app.
Qed.

Lemma scanl_not_nil: forall A B (op:A->B->A) e l, scanl op e l <> [].
Proof.
  destruct l; autounfold with sydpacc; simpl; intros; discriminate.
Qed.

Lemma scanl_app_gen:
  forall A B `{Monoid A op e} (q:B->A) c (l1 l2 : list B),
    let op' := fun x y=>op x (q y) in
    scanl op' c (l1++l2) =
    removelast(scanl op' c l1) ++ map (op (List.last (scanl op' c l1) e)) (scanl op' e l2).
Proof.
  intros A B op e H q; revert H; revert e.
    induction l1 as [ | x xs IH ] using rev_ind; intros l2 op'.
  - simpl; unfold op'; now rewrite scanl_map_gen with (e:=e) by typeclasses eauto.
  - rewrite associative, IH by auto; simpl. 
    rewrite scanl_snoc, removelast_app by (intro Heq; discriminate).
    simpl; rewrite app_nil_r, list_last_app; simpl.
    rewrite @right_neutral with (op:=op) by typeclasses eauto.
    rewrite app_removelast_last with (l:=scanl op' c xs)(d:=e) by (apply scanl_not_nil).
    rewrite associative; simpl.
    do 2 f_equal.
    assert(List.last (scanl op' c xs) e =
           List.fold_left op' xs c) as HH
      by now erewrite <- scanl_last_snd, <- list_last_scanl.
    fold op'. rewrite HH; clear HH.
    rewrite fold_left_app; simpl.
    generalize (fold_left op' xs e); intro a.
    replace (op e (q x)) with (op' e x) by (now unfold op').
    replace (op' e x) with (q x) by now (unfold op'; rewrite left_neutral).
    assert(forall x, scanl op' x l2 = map (op x) (scanl op' e l2)) as HH.
    {
      induction l2; intros x0.
      - simpl; f_equal; now rewrite  right_neutral.
      - simpl; f_equal.
        + now rewrite  right_neutral.
        + rewrite IHl2 with (x:=op' e a0).
          rewrite IHl2.
          rewrite map_map.
          apply map_ext; intros; unfold op'; simpl.
          rewrite associative, @left_neutral with(e:=e) by typeclasses eauto.
          trivial.
    }
    rewrite HH; rewrite map_map; apply map_ext; intro.
    unfold op'. now rewrite associative.
Qed.

Lemma scanl_app:
  forall `{Monoid A op e} (l1 l2 : list A),
    scanl op e (l1++l2) =
    removelast(scanl op e l1) ++ map (op (List.last (scanl op e l1) e)) (scanl op e l2).
Proof.
  intros A op e H l1 l2.
  now apply scanl_app_gen.
Qed.

Open Scope N_scope.

Lemma scanl_nlength:
  forall (A B:Type)(op:A->B->A)(identity:A)(l:list B),
    length (scanl op identity l) = N.succ (length l).
Proof.  
  intros A B op identity l; generalize dependent identity; induction l; intros.
  - trivial.
  - simpl; rewrite IHl; simpl; trivial.
Qed.

Arguments scanl_nlength [A B].

#[export] Hint Rewrite scanl_nlength : length.

Lemma scanl_fold:
  forall (A B:Type)(op:A->B->A)(identity:A)(l:list B)(index:N)(default:A), 
    ( index < 1 + length l) ->
    nth index (scanl op identity l) default = 
        List.fold_left op (firstn index l) identity.
Proof.
  intros A B op identity l index default valid_index;
    generalize dependent identity; generalize dependent index; induction l as [ | a l IHl ].
  - intros index valid_index identity;
      rewrite firstn_nil; simpl in *; destruct index; trivial.
    lia.
  - intros index valid_index identity; simpl; destruct index; simpl.
    + trivial.
    + rewrite IHl; trivial.
      rewrite length_cons in valid_index.
      rewrite N.pos_pred_spec.
      assert(N.pred (1+ (1+length l)) = 1 + length l) as H
        by (now rewrite N.add_1_l, N.pred_succ).
      rewrite <- H.
      apply N.pred_lt_mono in valid_index; auto.
      clear; intro H; discriminate.
Qed.

Fixpoint scan' {A B:Type}(op:A->B->A)(identity:A)(l:list B) : list A := 
  match l with 
    | []   => []
    | h::t =>let id := (op identity h) in id::scan' op id t
  end.

Lemma scan'_length:
  forall (A B : Type)(op:A->B->A)(identity:A)(l:list B),
    length (scan' op identity l) = length l.
Proof.  
  intros A B op identity l; generalize dependent identity; induction l as [ | a l IHl ].
  - intros; trivial. 
  - intros; simpl; rewrite IHl; simpl; trivial.
Qed.

#[export] Hint Rewrite scan_length : length.

Lemma scan_fold:
  forall (A B:Type)(op:A->B->A)(identity:A)(l:list B)(default:A) (index:N), 
    index < length l ->
    nth index (scan' op identity l) default = 
    List.fold_left op (firstn (1+index) l) identity.
Proof.
  intros A B op identity l default index validIndex; 
    generalize dependent identity; generalize dependent index; induction l.
  - intros; rewrite firstn_nil; simpl in *; destruct index; trivial;
    lia.
  - intros index validIndex identity; destruct index.
    + simpl; rewrite firstn_equation; trivial.
    + rewrite firstn_equation.
      destruct(1 + N.pos p) eqn:Heq.
      * lia.
      * simpl; rewrite IHl.
        -- repeat f_equal. repeat rewrite N.pos_pred_spec; rewrite <- Heq.
           rewrite N.add_pred_r; auto; lia.
        -- rewrite N.pos_pred_spec. rewrite length_cons in validIndex.
           apply N.pred_lt_mono in validIndex; trivial.
           rewrite N.add_1_l in validIndex.
           now rewrite N.pred_succ in  validIndex.
           clear; intro H; lia.
Qed.

(*-----------------------------------------------------------------*)

(** * Reduce on Arbitrary Lists and Properties *)

Definition reduce A (op:A -> A -> A) `{Monoid A op e} := 
  fun l => fold_left op l e.

Arguments reduce [A] op {e }{_}.

Set Implicit Arguments.

Lemma reduce_eq:
  forall A (op:A->A->A) (e:A) `{Monoid A op e} (x:A) (xs:list A),
    reduce op (x::xs) = op x (reduce op xs).
Proof.
  intros A op e H x xs.
  unfold reduce; simpl.
  replace (op e x) with (x) by now rewrite left_neutral.
  rewrite <- fold_left_prop.
  + f_equal; now rewrite right_neutral.
  + typeclasses eauto.
Qed.

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

#[export] Program Instance homomorphic_restrict_assoc `{Homomorphic A B h op}
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

#[export] Program Instance homomorphic_restrict_neutral `{Homomorphic A B h op}  
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

#[export] Program Instance homomorphic_restrict_monoid `{Homomorphic A B h op} 
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

#[export] Instance non_optimised_f `{Homomorphic A B h op} : Optimised_f h.
Proof. constructor. eexists. reflexivity. Qed.

#[export] Instance non_optimised_op `{Homomorphic A B h op} : Optimised_op h.
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
  - autounfold with sydpacc in *; unfold of_img in *; simpl in *.
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

#[export] Instance third_homomorphism_theorem_right_inverse
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

(*-----------------------------------------------------------------*)

(** * A Typeclass to Characterize Empty Lists *)

Class NonEmpty `(l:list A) := { non_emptiness : l<> [] }.

Ltac empty := 
  let H := fresh "Hempty" in 
  assert(H:=non_emptiness); contradict H; trivial.

(** ** Instances *)

#[export] Program Instance cons_non_empty 
        `(x:A)(xs:list A) : NonEmpty (x::xs).

#[export] Program Instance map_non_empty 
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

#[export] Instance app_non_empty_l 
         {A:Type}(l1 l2:list A){HNE:NonEmpty l1} : NonEmpty (l1++l2).
Proof.
  constructor; destruct HNE as [HNE]; contradict HNE.
  now apply app_eq_nil in HNE.
Qed.

#[export] Instance app_non_empty_r 
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

#[export] Instance length_lt_0_NonEmpty `(Hlt: (0 < n)%N) `{l:{l:list A | length l = n}} :
  NonEmpty (proj1_sig l).
Proof.
  destruct l as [ [ | h t] Hl ]; simpl in *.
  - lia.
  - typeclasses eauto.
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

(** ** [last] on NonEmpty lists *)

Unset Implicit Arguments.

Program Definition hd A (l:list A) `{NonEmpty A l} : A :=
  match l with
  | [ ] => _
  | h::t => h
  end.
Next Obligation.
  inversion H; contradiction.
Defined.

Arguments hd [A] l { _ }.

Definition last A (l:list A) `{NonEmpty A l} : A :=
  List.last l (hd l).

Arguments last [A] l { _ }.

#[export] Hint Unfold last : sydpacc.

Set Implicit Arguments.

(** ** Properties of [List.last] and [last] *)

Lemma list_last_non_empty:
  forall A l (d:A) d',
    NonEmpty l ->
    List.last l d = List.last l d'.
Proof.
  intros A; induction l as [ | x xs IH]; intros d d' H.
  - inversion H; contradiction.
  - simpl; destruct xs; trivial.
    apply IH.
    typeclasses eauto.
Qed.
  
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

Lemma last_pi:
  forall A l l' Hl Hl',
    l = l' ->
    @last A l Hl = @last A l' Hl'.
Proof.
  intros A l l' Hl Hl' H.
  autounfold with sydpacc; f_equal; auto.
  destruct l.
  - inversion Hl; contradiction.
  - destruct l'.
    + inversion Hl'; contradiction.
    + inversion H; subst.
      auto.
Qed.

Lemma last_cons_non_empty:
  forall `{NonEmpty A xs} x,
    last (x::xs) = last xs.
Proof.
  intros A xs H x. revert  x.
  induction xs; autounfold with sydpacc in *; simpl; intro x.
  - inversion H; contradiction.
  - simpl in IHxs. destruct xs.
    + trivial.
    + simpl in *. specialize (IHxs (cons_non_empty a0 xs)).
      rewrite IHxs. symmetry. now rewrite IHxs.
Qed.


Lemma last_app:
  forall A (xs:list A) x,
    last (xs++[x]) = x.
Proof.
  intros A xs x; unfold last.
  apply list_last_app.
Qed.

Lemma last_map:
  forall A B (f:A->B) `{NonEmpty A l},
    last (map f l) = f (last l).
Proof.
  intros A B f; induction l as [ | h t IH ]; intros H.
  - inversion H; contradiction.
  - destruct t; simpl.
    + trivial.
    + erewrite last_pi by reflexivity; rewrite last_cons_non_empty. 
      simpl in IH; specialize (IH _);
        erewrite last_pi in IH by reflexivity.
      rewrite IH.
      f_equal; symmetry;
        erewrite last_pi at 1 by reflexivity.
      apply last_cons_non_empty.
Qed.

Lemma removelast_length:
  forall A (l:list A), List.length(removelast l) = pred(List.length l).
Proof.
  intros A l;induction l as [ | h t IH ].
  - trivial. 
  - destruct t as [ | a t ].
    + trivial.
    + replace (h::a::t) with ([h]++(a::t)) by auto.
      rewrite removelast_app by (intro HH; discriminate).
      repeat rewrite List.app_length.
      now rewrite IH by typeclasses eauto.
Qed.
Lemma removelast_length_N:
  forall `(l:list A),
    length(removelast l) = N.pred(length l).
Proof.
  intros A; induction l as [ | h t IH ].
  - trivial.
  - destruct t.
    + trivial.
    + replace (h::a::t) with ([h]++(a::t)) by auto.
      rewrite removelast_app by (intro HH; discriminate).
      autorewrite with length. rewrite IH by typeclasses eauto.
      repeat rewrite N.add_1_l; simpl.
      now repeat rewrite N.pred_succ.
Qed.

#[export] Hint Rewrite @removelast_length @removelast_length_N : length.

Lemma fst_scanl_last_length:
  forall (A B:Type)(op:A->B->A)(e:A)(l:list B),
    List.length(fst (scanl_last op e l)) = List.length l.
Proof.
  intros A B op e l.
  rewrite scanl_last_fst_scanl.
  now autorewrite with length.
Qed.

#[export] Hint Rewrite fst_scanl_last_length : length.

#[export] Instance prefix_non_empty `(xs:list A) : NonEmpty (prefix xs).
Proof.
  constructor; intro H; destruct xs; simpl; discriminate.
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


Lemma scanl_removelast:
  forall A B (op:A->B->A) e `{ NonEmpty B l},
    removelast (scanl op e l) = scanl op e (removelast l).
Proof.
  intros A B op e l H; revert e; induction l as [ | h t IH ]; intro e.
  - empty.
  - destruct t.
    + trivial.
    + set(t':=b::t) in *.
      replace (scanl op e (h::t')) with ([ e ] ++ scanl op (op e h) t') by auto.
      replace (h::t') with ([h]++t') by auto.
      rewrite removelast_app by apply non_emptiness.
      rewrite removelast_app by (unfold t'; apply non_emptiness).
      now rewrite IH by (unfold t'; typeclasses eauto).
Qed.

#[export] Instance scanl_non_empty A B (op:A->B->A) e l : NonEmpty (scanl op e l).
Proof. 
  constructor; now apply scanl_not_nil.
Qed.

Fact scanl_hd:
  forall A B (op:A->B->A) e l,
    hd (scanl op e l) = e.
Proof.
  intros A B op e l; now destruct l.
Qed.

#[export] Instance scanl'_non_empty A B (op:A->B->A) e l : NonEmpty (scanl' op e l).
Proof.
  rewrite <- scanl_scanl'.
  typeclasses eauto.
Qed.

#[export] Instance scan_non_empty A `{Monoid A op e} l : NonEmpty (scan op l).
Proof.
  destruct l; autounfold; simpl; constructor; intros; discriminate.
Qed.

Lemma last_scanl:
  forall A B (op:A->B->A) e xs,
    last(scanl op e xs) = snd(scanl_last op e xs).
Proof.
  intros A B op e xs.
  transitivity (last(fst (scanl_last op e xs)++[snd(scanl_last op e xs)])).
  - apply last_pi, scanl_scanl_last.
  - apply last_app.
Qed.

Close Scope N_scope.

Close Scope sydpacc_scope.

