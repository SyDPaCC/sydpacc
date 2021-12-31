Require Import SyDPaCC.Core.Bmf.
Require Import Program Lia Bool NArith (*Classical_Pred_Type*).

Set Implicit Arguments.

Open Scope sydpacc_scope.
Open Scope N.

(* * Binary Trees: Type and Properties *)

(* ** Binary Trees: Definition *)

Inductive t (A B: Type) :=
| Leaf : A -> t A B
| Node : B -> t A B -> t A B -> t A B.

Arguments Leaf [A B].

(* ** Binary Trees: Same Form Property *)

Inductive same_form {A B C D:Type} : t A B -> t C D ->  Prop :=
| sfi_leaf :
    forall a1 a2,
      same_form (Leaf a1) (Leaf a2)
| sfi_node :
    forall a1 a2 l1 r1 l2 r2,
      same_form l1 l2
      -> same_form r1 r2
      -> same_form (Node a1 l1 r1) (Node a2 l2 r2).


Lemma same_form_trans :
  forall A B C D E F (t1:t A B) (t2:t C D) (t3:t E F),
    same_form t1 t2 -> same_form t2 t3 -> same_form t1 t3.
Proof.
  intros A B C D E F tree1;
    induction tree1; intros tree2 tree3;
    destruct tree2, tree3; intros H1 H2;
    try solve [ constructor ];
    try solve [ inversion H1 ] ;
    try solve [ inversion H2 ].
  inversion H1; inversion H2; subst; constructor;
    eauto using IHtree1_1, IHtree1_2.
Qed.

Arguments same_form_trans [A B C D E F].

Class Same_Form {A B C D} (t1: t A B) (t2: t C D) :=
  MkSF
    {
      c_same_form : same_form t1 t2
    }.


Class Same_Form_RT {A B C D} (t1: t A B) (t2:t C D) {H: Same_Form t1 t2}.

Generalizable All Variables.

#[export] Instance Same_Form_Trans {A B C D E F} (t1:t A B) (t2:t C D) (t3:t E F)
         {H1:Same_Form t1 t2} `{H2: @Same_Form_RT _ _ _ _ t2 t3 H}:
  @Same_Form_RT _ _ _ _ t1 t3
                (MkSF (same_form_trans t1 t2 t3
                                       (c_same_form (Same_Form := H1))
                                       (@c_same_form _ _ _ _ _ _ H))).
Defined.

#[export] Instance sameform_node_left {A B C D:Type} (a1:B) (l1 r1:t A B) (a2:D) (l2 r2:t C D) t1 t2:
  t1 = Node a1 l1 r1 ->
  t2 = Node a2 l2 r2 ->
  Same_Form t1 t2 -> Same_Form l1 l2.
Proof.
  intros H1 H2 Hsf; subst. inversion Hsf; inversion c_same_form0.
  constructor; assumption.
Qed.

#[export] Instance sameform_node_right {A B C D:Type} (a1:B) (l1 r1:t A B) (a2:D) (l2 r2:t C D) t1 t2:
  t1 = Node a1 l1 r1 ->
  t2 = Node a2 l2 r2 ->
  Same_Form t1 t2 -> Same_Form r1 r2.
Proof.
  intros H1 H2 Hsf; subst. inversion Hsf; inversion c_same_form0.
  constructor; assumption.
Qed.

#[export] Instance sameform_node_left'
         {A B C D:Type} (a1:B) (l1 r1:t A B) (a2:D) (l2 r2:t C D)
         {H: Same_Form (Node a1 l1 r1) (Node a2 l2 r2)}
  : Same_Form l1 l2.
Proof.
  eapply sameform_node_left; eauto.
Qed.

#[export] Instance sameform_node_right'
         {A B C D:Type} (a1:B) (l1 r1:t A B) (a2:D) (l2 r2:t C D)
         { H:Same_Form (Node a1 l1 r1) (Node a2 l2 r2)}
  : Same_Form r1 r2.
Proof.
  eapply sameform_node_right; eauto.
Qed.

Lemma not_same_form_tn:
  forall (A B C D: Type) (a:A) (d:D) (r l:t C D) (t1:t A B) (t2:t C D),
    t1 = Leaf a ->
    t2 = Node d r l ->
    not(Same_Form t1 t2).
Proof.
  intros; subst; intro HH; inversion HH as [ H' ]; inversion H'.
Qed.

Lemma not_same_form_nt:
  forall (A B C D: Type) (a:A) (d:D) (r l:t C D) t1 (t2:t A B),
    t2 = Leaf a ->
    t1 = Node d r l ->
    not(Same_Form t1 t2).
Proof.
  intros; subst; intro HH; inversion HH as [ H' ]; inversion H'.
Qed.

(** * Functions on Binary Trees *)

(** ** Specifications *)

Module Spec.
  
  Fixpoint size `(tree: t A B) : N :=
    match tree with
    | Leaf _ => 1
    | Node _ l r => 1 + (size l) + (size r)
    end.
  
  Fixpoint map (A B C D :Type) (kL:A -> C)(kN:B -> D)(tree: t A B): t C D :=
    match tree with
    | Leaf n => Leaf (kL n)
    | Node n l r => Node (kN n) (map kL kN l) (map kL kN r)
    end.
  
  Fixpoint mapt (A B C D:Type) (kL: A -> C)
           (kN: B -> t A B -> t A B -> D) (tree:t A B) : t C D :=
    match tree with
    | Leaf n =>  Leaf (kL n)
    | Node n l r => Node (kN n l r) (mapt kL kN l) (mapt kL kN r)
    end.

  (* TODO: change the type of k to A -> B -> A -> A *)
  Fixpoint reduce (A B:Type) (k: A * B * A -> A)(tree: t A B): A :=
    match tree with
    | Leaf n => n
    | Node n l r => k (reduce k l, n, reduce k r)
    end.

    (* TODO: change the type of k to A -> B -> A -> A *)
  Fixpoint uAcc (A B : Type) (k: A * B * A -> A)(tree: t A B): t A A :=
    match tree with
    | Leaf n => Leaf n
    | Node n l r => let n' := reduce k tree in
                   Node n' (uAcc k l) (uAcc k r)
    end.

    (* TODO: change the type of gl, gr to C -> B -> C *)
  Fixpoint dAcc (A B C:Type) (gl gr:C * B -> C) (c:C) (tree: t A B): t C C :=
    match tree with
    | Leaf n => Leaf c
    | Node n l r =>
      let l' := dAcc gl gr (gl (c,n)) l in
      let r' := dAcc gl gr (gr (c,n)) r in
      Node c l' r'
    end.
  
  Program Fixpoint zip (A B C D:Type) (tree1 : t A B) (tree2 : t C D) (H: Same_Form tree1 tree2)
    : t (A*C) (B*D) :=
    match (tree1,tree2) with
    | (Leaf a, Leaf c) => Leaf (a,c)
    | (Node b l1 r1, Node d l2 r2) =>
      let l := (zip (@sameform_node_left _ _ _ _ b l1 r1 d l2 r2 _ _ _ _  H)) in
      let r := (zip (@sameform_node_right _ _ _ _ b l1 r1 d l2 r2 _ _ _ _ H)) in
      Node (b,d) l r
    | _ => _
    end.
  Next Obligation.
    inversion H.
    destruct tree1, tree2.
    + contradiction H1 with (a0:=a) (c0:=c). reflexivity.
    + contradict H; intro H; inversion H; inversion c_same_form0.
    + contradict H; intro H; inversion H; inversion c_same_form0.
    + contradiction H0 with (b0:=b) (l1:=tree1_1) (r1:=tree1_2)
                            (d0:=d) (l2:=tree2_1) (r2:=tree2_2); reflexivity.
  Defined.
  Next Obligation.
    split; intros; discriminate.
  Defined.
  Next Obligation.
    inversion H; split; intros; discriminate.
  Defined.

  Arguments zip [A B C D] tree1 tree2 {H}.
  
End Spec.

(** ** Tail-Recursive Definitions *)

Definition root {A:Type} (tree : t A A) : A :=
  match tree with
  | Leaf a => a
  | Node b _ _ => b
  end.

(* ====================================== *)
(* TODO: externalize all the internal fix *)
(* ====================================== *)

Fixpoint size_aux (A B: Type) (tree:t A B)(k: N -> N) :=
  match tree with
  | Leaf _ => k 1
  | Node _ l r =>
    size_aux l (fun lm => size_aux r (fun rm =>k (1 + lm + rm)))
  end.
      
Definition size (A B:Type) (tree: t A B) : N :=
  size_aux tree (fun x => x).

Fixpoint map_aux (A B C D:Type) (kL : A -> C) (kN : B -> D) (tree: t A B) (k: t C D -> t C D) : t C D :=
  match tree with
  | Leaf a => k (Leaf (kL a))
  | Node b l r => 
    map_aux kL kN l (fun lm => map_aux kL kN r (fun rm => k(Node (kN b) lm rm)))
  end.
  
Definition map (A B C D:Type) (kL : A -> C) (kN : B -> D) (tree: t A B) : t C D :=
  map_aux kL kN tree (fun x => x).

Fixpoint mapt_aux (A B C D:Type) (kL: A -> C) (kN: B -> t A B -> t A B -> D) (tree:t A B) (k: t C D -> t C D) :=
  match tree with
  | Leaf a => k (Leaf (kL a))
  | Node b l r =>
    mapt_aux kL kN l (fun lm => mapt_aux kL kN r (fun rm => k(Node (kN b l r) lm rm)))
  end.

Definition mapt (A B C D:Type) (kL: A -> C) (kN: B -> t A B -> t A B -> D) (tree:t A B) : t C D :=
  mapt_aux kL kN tree (fun x => x).

Fixpoint reduce_aux (A B: Type)(kr: A * B * A -> A)(tree: t A B) (k:A->A) : A :=
  match tree with
  | Leaf a => k a
  | Node b l r =>
    reduce_aux kr l (fun lm => reduce_aux kr r (fun rm => k( kr (lm,b,rm))))
  end.

Definition reduce (A B: Type)(kr: A * B * A -> A)(tree: t A B): A :=
  reduce_aux kr tree (fun x => x).

Fixpoint uAcc_aux (A B : Type) (ka: A * B * A -> A) (tree:t A B) (k: t A A -> t A A) :=
  match tree with
  | Leaf a => k (Leaf a)
  | Node b l r =>
    uAcc_aux ka l (fun lm => uAcc_aux ka r (fun rm => k(Node (ka ((root lm),b,(root rm))) lm rm )))
  end.

Definition uAcc (A B : Type) (ka: A * B * A -> A)(tree: t A B): t A A :=
  uAcc_aux ka tree (fun x => x).

Fixpoint dAcc_aux (A B C: Type) (gl gr:C * B -> C) (c:C) (tree: t A B) (k: t C C -> t C C) :=
  match tree with
  | Leaf n => k (Leaf c)
  | Node n l r =>
    dAcc_aux gl gr (gl (c,n)) l (fun lm => dAcc_aux gl gr (gr (c,n)) r (fun rm => k(Node c lm rm)))
  end.

Definition dAcc (A B C: Type) (gl gr:C * B -> C) (c:C) (tree: t A B) : t C C :=
  dAcc_aux gl gr c tree (fun x => x).

Fixpoint zip_aux (A B C D:Type) (tree1 : t A B) (tree2 : t C D) {HH: Same_Form tree1 tree2}
         (k:  t (A*C) (B*D) ->  t (A*C) (B*D)) :=
  (match (tree1,tree2) as pair return tree1 = (fst pair) -> tree2 = (snd pair) -> t (A*C) (B*D) with
   | (Leaf a, Leaf c) => fun _ _ => k (Leaf (a,c))
   | (Node b l1 r1, Node d l2 r2) =>
     fun H1 H2 =>
       zip_aux (HH := @sameform_node_left _ _ _ _ b l1 r1 d l2 r2 _ _ H1 H2 HH)
               (fun lm => zip_aux (HH := @sameform_node_right _ _ _ _ b l1 r1 d l2 r2 _ _ H1 H2 HH)
                               (fun rm => k(Node (b,d) lm rm)))
   | (Leaf a, Node d l r) =>
     fun H1 H2 =>  False_rect _ (not_same_form_tn H1 H2 HH)
   | (Node d l r, Leaf a) => fun H1 H2 => False_rect _ (not_same_form_nt H2 H1 HH)
   end) eq_refl eq_refl.

Arguments zip_aux [A B C D] tree1 tree2 {HH} k.

Definition zip (A B C D:Type) (tree1 : t A B) (tree2 : t C D) {H: Same_Form tree1 tree2}
  : t (A*C) (B*D) :=
  zip_aux tree1 tree2 (fun x => x) (HH:=H).

Arguments zip [A B C D] tree1 tree2 {H}.

(** ** Correctness of Tail-Recursive Definitions  *)

Section EqSpec.

  (* ================================================================ *)
  (* TODO: Auxiliary lemmas about the auxiliary recursive definitions *)
  (* ================================================================ *)

  Lemma size_aux_prop:
    forall `(tree:t A B) f,
      size_aux tree f = f(Spec.size tree).
  Proof.
    intros A B tree. induction tree as [ a | a l IHl r IHr ]; intro f; simpl.
    - trivial.
    - rewrite IHl, IHr; trivial.
  Qed.
  
  Lemma size_spec_size :
    forall `(tree:t A B),
      size tree = Spec.size tree.
  Proof.
    unfold size. intros A B tree.
    now rewrite size_aux_prop.
  Qed.
  
  Lemma map_aux_prop:
    forall A B C D (kL:A->C) (kN:B->D) (tree:t A B) (k:t C D->t C D),
      map_aux kL kN tree k = k(Spec.map kL kN tree).
  Proof.
    intros A B C D kL kN tree.
    induction tree as [ a | a l IHl r IHr ]; intro k; simpl.
    - trivial.
    - rewrite IHl, IHr; trivial.
  Qed.
  
  Lemma map_spec_map :
    forall `(kL : A -> C) `(kN : B -> D) (tree: t A B),
      map kL kN tree = Spec.map kL kN tree.
  Proof.
    unfold map; intros; now rewrite map_aux_prop.
  Qed.

  Lemma mapt_aux_prop:
    forall `(kL: A -> C) `(kN: B -> t A B -> t A B -> D) (tree:t A B) k,
      mapt_aux kL kN tree k = k(Spec.mapt kL kN tree).
  Proof.
    intros A C kL B D kN tree; 
      induction tree as [ a | a l IHl r IHr ]; intro k; simpl.
    - trivial.
    - rewrite IHl, IHr; trivial.
  Qed.
  
  Lemma mapt_spec_mapt: forall `(kL: A -> C) `(kN: B -> t A B -> t A B -> D) (tree:t A B),
      mapt kL kN tree = Spec.mapt kL kN tree.
  Proof.
    unfold mapt; intros; now rewrite mapt_aux_prop.
  Qed.

  Lemma reduce_aux_prop:
    forall `(kr: A * B * A -> A)(tree: t A B) k,
      reduce_aux kr tree k = k (Spec.reduce kr tree).
  Proof.
    intros A B kr tree; 
      induction tree as [ a | a l IHl r IHr ]; intro k; simpl.
    - trivial.
    - rewrite IHl, IHr; trivial.
  Qed.
  
  Lemma reduce_spec_reduce: forall (A B: Type)(kr: A * B * A -> A)(tree: t A B),
      reduce kr tree = Spec.reduce kr tree.
  Proof.
    unfold reduce; intros; now rewrite reduce_aux_prop.
  Qed.

  Lemma uAcc_aux_prop:
    forall (A B : Type) (ka: A * B * A -> A)(tree: t A B) k,
      uAcc_aux ka tree k = k(Spec.uAcc ka tree).
  Proof.
    intros A B ka tree; 
    induction tree as [ a | a l IHl r IHr ]; intro k; simpl.
    - trivial.
    - rewrite IHl, IHr; simpl; repeat f_equal;
      match goal with
      | [ |- _ = Spec.reduce _ ?tree] => destruct tree; auto
      end.
  Qed.
  
  Lemma uAcc_spec_uAcc: forall (A B : Type) (ka: A * B * A -> A)(tree: t A B),
      uAcc ka tree = Spec.uAcc ka tree.
  Proof.
    unfold uAcc; intros; now rewrite uAcc_aux_prop.
  Qed.

  Lemma dAcc_aux_prop:
    forall (A B C: Type) (gl gr:C * B -> C) (tree: t A B) c k,
      dAcc_aux gl gr c tree k = k(Spec.dAcc gl gr c tree).
  Proof.
    intros A B C gl gr tree.
    induction tree as [ a | a l IHl r IHr ]; intros c k; simpl.
    - trivial.
    - rewrite IHl, IHr; trivial.
  Qed.
  
  Lemma dAcc_spec_dAcc: forall (A B C: Type) (gl gr:C * B -> C) (c:C) (tree: t A B),
      dAcc gl gr c tree = Spec.dAcc gl gr c tree.
  Proof.
    unfold dAcc; intros; now rewrite dAcc_aux_prop.
  Qed.


  Lemma zip_aux_prop:
    forall (A B C D:Type) (t1: t A B) (t2: t C D) {H:Same_Form t1 t2} k,
      zip_aux t1 t2 k (HH:=H) = k(Spec.zip t1 t2 (H:=H)).
  Proof.
    intros A B C D t1; induction t1 as [ a1 | a1 l1 IHl1 r1 IHr1]; intros [ a2 | a2 l2 r2 ] H k.
    - trivial.
    - contradict H. eapply not_same_form_tn; eauto.
    - contradict H. eapply not_same_form_nt; eauto.
    - simpl; now rewrite IHl1, IHr1.
  Qed.


  Lemma zip_spec_zip: forall (A B C D:Type) (t1: t A B) (t2: t C D) {H:Same_Form t1 t2},
      zip t1 t2 (H:=H) = Spec.zip t1 t2 (H:=H).
  Proof.
    unfold zip; intros; now rewrite zip_aux_prop.
  Qed.
  
End EqSpec.

(** ** Preservation of the Same Form Property *)

#[export] Instance same_form_map {A B C D} (kL : A -> C) (kN : B -> D) (tree:t A B) :
  Same_Form tree (map kL kN tree).
Proof.    
  induction tree as [| x tl Hl tr Hr].
  + simpl. constructor; apply sfi_leaf.
  + simpl. constructor.
    rewrite map_spec_map.
    rewrite map_spec_map in Hr, Hl.
    apply sfi_node.
    ++ inversion Hl; assumption.
    ++ inversion Hr; assumption. 
Qed.

#[export] Instance same_form_mapt {A B C D} (kL : A -> C)  (kN: B -> t A B -> t A B -> D) (tree:t A B) :
  Same_Form tree (mapt kL kN tree).
Proof.    
  induction tree as [| x tl Hl tr Hr].
  + simpl. constructor; apply sfi_leaf.
  + simpl. constructor.
    rewrite mapt_spec_mapt. rewrite mapt_spec_mapt in Hl, Hr.
    apply sfi_node.
    ++ inversion Hl; assumption.
    ++ inversion Hr; assumption.
Qed.

#[export] Instance same_form_uAcc {A B} (k: A * B * A -> A)(tree: t A B) :
  Same_Form tree (uAcc k tree).
Proof.
  induction tree as [| x tl Hl tr Hr].
  + simpl. constructor; apply sfi_leaf.
  + simpl; constructor.
    rewrite uAcc_spec_uAcc; rewrite uAcc_spec_uAcc in Hr, Hl.
    apply sfi_node.
    ++ inversion Hl; assumption.
    ++ inversion Hr; assumption.
Qed.  

#[export] Instance same_form_dAcc {A B C} (gl gr:C * B -> C) (c:C) (tree: t A B) :
  Same_Form tree (dAcc gl gr c tree).
Proof.
  generalize dependent c. induction tree as [| a l IHl r IHr].
  - simpl. constructor; apply sfi_leaf.
  - intro c. rewrite dAcc_spec_dAcc. 
    simpl. repeat rewrite <- dAcc_spec_dAcc. 
    constructor; apply sfi_node.
    + apply IHl.
    + apply IHr. 
Qed.

#[export] Instance same_form_comp {A B C D E F} (tree1: t A B)
         (f: t A B -> t C D) (g: t C D -> t E F)
         {Hf_sf: forall x, Same_Form x (f x)} {Hg_sf: forall x, Same_Form x (g x)} :
  Same_Form tree1 ((g ∘ f) tree1).
Proof.
  autounfold. constructor.
  apply same_form_trans with (t2:=f tree1).
  apply c_same_form. apply Hg_sf.
Qed.

Close Scope N.
Close Scope sydpacc_scope.
