Require Import SyDPaCC.Core.Bmf.
Require Import Coq.Lists.List NArith Bool Program Lia.
Import ListNotations. 
From SyDPaCC.Tree Require Import Closure BTree.
From SyDPaCC.Support Require Import Option List UIP.
Require Import SyDPaCC.Core.Parallelization.
Require Import SyDPaCC.Tree.Support.NOption.

Set Implicit Arguments.
Generalizable All Variables.

Open Scope sydpacc_scope.
Open Scope N_scope.

(** * Preambule: to move to the appropriate files *)

#[export] Hint Rewrite @size_spec_size @map_spec_map @mapt_spec_mapt
       @zip_spec_zip @dAcc_spec_dAcc @uAcc_spec_uAcc : tree.


#[export] Instance same_form_eq A B C D
         (t1 t1': t A B)(t2 t2': t C D) (H: Same_Form t1 t2) 
         (H1: t1 = t1') (H2: t2 = t2') : Same_Form t1' t2'.
Proof.
  inversion H as [ HH ]; constructor; clear H.
  now subst.
Defined.

Lemma spec_zip_pi:
  forall A B C D (t1: t A B)(t2: t C D) (H H': Same_Form t1 t2),
    Spec.zip t1 t2 (H:=H) = Spec.zip t1 t2 (H:=H').
Proof.
  intros A B C D t1.
  induction t1 as [ v1 | v1 l1 IHl1 r1 IHr1 ];
    intros  t2 H H';
    destruct t2 as [ v2 | v2 l2 r2 ]; unfold zip; simpl.
  - trivial.
  - contradict H. eapply not_same_form_tn; eauto.
  - contradict H. eapply not_same_form_nt; eauto.
  - f_equal; [ apply IHl1 | apply IHr1 ].
Qed.

    
Lemma zip_eq:
  forall A B C D (t1 t1': t A B)(t2 t2': t C D) (H: Same_Form t1 t2)
    (H1: t1 = t1') (H2: t2 = t2'),
    zip t1 t2 (H:=H) = zip t1' t2' (H:=same_form_eq H H1 H2).
Proof.
  intros A B C D t1 t1' t2 t2' H H1 H2.
  autorewrite with tree.
  generalize dependent t2'.
  generalize dependent t2.
  generalize dependent t1'.
  induction t1 as [ v1 | v1 l1 IHl1 r1 IHr1 ];
    intros t1' H1 t2 H t2' H2;
    destruct t2 as [ v2 | v2 l2 r2 ].
  - now subst.
  - contradict H. eapply not_same_form_tn; eauto.
  - contradict H. eapply not_same_form_nt; eauto.
  - subst; simpl; f_equal; apply spec_zip_pi.
Qed.

Lemma size_reduce:
  forall A B t,
    Spec.size t =
    Spec.reduce (fun arg : N * N * N => let (p, c) := arg in let (a, b) := p in a + b + c) (Spec.map (fun _ : A => 1) (fun _ : B => 1) t).   
Proof.
  intros A B; induction t as [ v | v l IHl r IHr ].
  - trivial.
  - simpl Spec.reduce. rewrite <- IHl, <- IHr.
    replace (Spec.size (Node v l r)) with (1 + Spec.size l + Spec.size r) by auto.
    lia.
Qed.


Definition is_critical (m:N) (size size_l size_r: N) : bool :=
  let quo_l := size_l / m in
  let quo_r := size_r / m in
  let quo := size / m in
  let rem_l := size_l mod m in
  let rem_r := size_r mod m in
  let rem := size mod m in
  let val_l := quo_l + if rem_l =? 0 then 0 else 1 in
  let val_r := quo_r + if rem_r =? 0 then 0 else 1 in
  let val := quo + if rem =? 0 then 0 else 1 in
  (val_l <? val) && (val_r <? val).

Lemma is_critical_1:
  forall size_l size_r,
    is_critical 1 (1+size_l+size_r) size_l size_r = true.
Proof.
  intros size_l size_r.
  unfold is_critical.
  repeat rewrite N.mod_1_r. 
  repeat rewrite N.div_1_r.
  replace (if 0=? 0 then 0 else 1)
    with 0 by auto.
  repeat rewrite N.add_0_r.
  apply andb_true_iff; split; apply N.ltb_lt; lia.
Qed.
  
Fact eq1:
  forall A B v l r,
    Spec.map (fun _ : A => 1) (fun _ : B => 1) (Node v l r) =
    Node 1
         (Spec.map (fun _ : A => 1) (fun _ : B => 1) l)
         (Spec.map (fun _ : A => 1) (fun _ : B => 1) r).
Proof. auto. Qed.

Fact eq2:
  forall A B v l r,
    Spec.uAcc (fun arg : N * N * N => let (p, c) := arg in let (a, b) := p in a + b + c) (Spec.map (fun _ : A => 1) (fun _ : B => 1) (Node v l r)) =
    Node (1+size l+size r)
         (Spec.uAcc (fun arg : N * N * N => let (p, c) := arg in let (a, b) := p in a + b + c) (Spec.map (fun _ : A => 1) (fun _ : B => 1) l))
         (Spec.uAcc (fun arg : N * N * N => let (p, c) := arg in let (a, b) := p in a + b + c) (Spec.map (fun _ : A => 1) (fun _ : B => 1) r)).
Proof.
  intros. rewrite eq1. simpl Spec.uAcc. f_equal.
  autorewrite with tree. repeat rewrite size_reduce.
  lia.
Qed.

Fact eq3:
  forall A B v l r m,
    Spec.mapt (fun _ : N => false) (fun (n : N) (l0 r0 : t N N) => is_critical m n (root l0) (root r0))
              (Spec.uAcc (fun arg : N * N * N => let (p, c) := arg in let (a, b) := p in a + b + c)
                         (Spec.map (fun _ : A => 1) (fun _ : B => 1) (Node v l r))) =
    Node (is_critical m (1+size l+size r) (size l) (size r))
         (Spec.mapt (fun _ : N => false) (fun (n : N) (l0 r0 : t N N) => is_critical m n (root l0) (root r0))
                    (Spec.uAcc (fun arg : N * N * N => let (p, c) := arg in let (a, b) := p in a + b + c) (Spec.map (fun _ : A => 1) (fun _ : B => 1) l)))
         (Spec.mapt (fun _ : N => false) (fun (n : N) (l0 r0 : t N N) => is_critical m n (root l0) (root r0))
                    (Spec.uAcc (fun arg : N * N * N => let (p, c) := arg in let (a, b) := p in a + b + c) (Spec.map (fun _ : A => 1) (fun _ : B => 1) r))).
Proof.
  intros A B v l r m.
  simpl Spec.mapt. f_equal. f_equal.
  - repeat rewrite <- size_reduce.
    autorewrite with tree.
    lia.
  - destruct l; simpl; auto.
    repeat rewrite <- size_reduce.
    autorewrite with tree.
    now rewrite N.add_comm with (m:=1).
  - destruct r; simpl; auto.
    repeat rewrite <- size_reduce.
    autorewrite with tree.
    now rewrite N.add_comm with (m:=1).
Qed.

(** * Linearized Trees *)

Inductive value A B :=
| Le : A -> value A B
| No : B -> value A B
| Cr : B -> value A B.

Arguments Le [A B].
Arguments No [A B].
Arguments Cr [A B].

Definition segment A B := list (value A B) .

Inductive node_type (A B:Type) :=
| Normal : A -> node_type A B
| Critical: B -> node_type A B.

Arguments Normal [A B].
Arguments Critical [A B].

Fixpoint no_critical `(tree: BTree.t (node_type A B) B) : bool :=
  match tree with
  | Leaf(Normal v) => true
  | Leaf(Critical v) => false
  | Node v l r => no_critical l && no_critical r
  end.

Inductive wf_segment A B: segment A B -> Prop :=
| wf_leaf : forall v:A, wf_segment [Le v]
| wf_critical: forall v:B, wf_segment [Cr v]
| wf_node : forall l1 l2 v,
    wf_segment l1 ->
    wf_segment l2 ->
(* (List.length (List.filter is_critical (l1++l2)) <= 1)%nat -> *)
    wf_segment ((No v)::l1++l2).

Section Serialization.

  Fixpoint spec_t2s `(tree: BTree.t A (node_type B B)) : list(segment A B):=
    match tree with
    | BTree.Leaf v => [[Le v]]
    | BTree.Node (Critical v) l r =>
      [[Cr v]] ++ (spec_t2s l) ++ (spec_t2s r)
    | BTree.Node (Normal v) l r =>
      match (spec_t2s l, spec_t2s r) with
      | (hl::tl,hr::tr) =>
        [ (No v)::hl++hr ] ++ tl ++ tr
      | _ => []
      end
    end.

  Lemma spec_t2s_all_wf:
    forall  `(tree: BTree.t A (node_type B B)),
    forall seg, In seg (spec_t2s tree) ->
           wf_segment seg.
  Proof.
    intros A B tree; induction tree as [ v | v l IHl r IHr]; intros seg Hin; simpl in *.
    - destruct Hin as [Hin | Hin ].
      + rewrite <- Hin. constructor.
      + inversion Hin.
    - destruct v as [ n | c ] eqn:Hv.
      + destruct(spec_t2s l) as [ | hl tl ] eqn:Hl;
          destruct(spec_t2s r) as [ | hr tr ] eqn:Hr;
          try solve [inversion Hin]; subst.
        simpl in Hin. destruct Hin as [Heq | Hin].
        * subst; constructor.
          -- apply IHl; simpl; auto.
          -- apply IHr; simpl; auto.
        * apply in_app_or in Hin.
          destruct Hin;
            [apply IHl | apply IHr]; simpl; auto.
      + simpl in Hin. destruct Hin as [Heq | Hin].
        * subst. constructor.
        * apply in_app_or in Hin.
          destruct Hin; auto.
  Qed.

  Fixpoint tree_to_segments_aux `(tree: BTree.t A (node_type B B))
           (k : list(segment A B) -> list(segment A B)) :
    list(segment A B) :=
    match tree with
    | BTree.Leaf v => k [[Le v]]
    | BTree.Node (Critical v) l r =>
      tree_to_segments_aux l (fun lm => tree_to_segments_aux r (fun rm => k([[Cr v]] ++ lm ++ rm)))
    | BTree.Node (Normal v) l r =>
      tree_to_segments_aux l (fun lm => tree_to_segments_aux r (fun rm =>
                                                 match lm, rm with
                                                 | hl::tl, hr::tr =>
                                                   k([[No v] ++ hl ++ hr] ++ tl ++ tr)
                                                 | _, _ => k []
                                                 end))
    end.
  
  Definition tree_to_segments `(tree: BTree.t A (node_type B B)) : list(segment A B) :=
    tree_to_segments_aux tree (fun x=>x).

  Lemma tree_to_segments_aux_prop:
    forall `(tree: BTree.t A (node_type B B)) f,
      tree_to_segments_aux tree f = f(spec_t2s tree).
  Proof.
    intros A B; induction tree as [ v | v l IHl r IHr ]; intro f; simpl.
    - trivial.
    - destruct v; rewrite IHl, IHr;
        destruct(spec_t2s l); destruct(spec_t2s r); auto.
  Qed.
      
  Lemma spec_t2s_tree_to_segments:
    forall `(tree: BTree.t A (node_type B B)),
      spec_t2s tree = tree_to_segments tree.
  Proof.
    intros; unfold tree_to_segments;
      now rewrite tree_to_segments_aux_prop.
  Qed.

  Definition annotate `(tree:BTree.t A B) (m:N) : BTree.t A (node_type B B) := 
    let f1 := BTree.map (fun x => 1) (fun x => 1) in
    let f2 := BTree.uAcc (fun arg => match arg with (a,b,c) => a+b+c end) in
    let f3 := BTree.mapt (fun x => false)
                         (fun n l r => let size_l := BTree.root l in
                                    let size_r := BTree.root r in
                                    is_critical m n size_l size_r) in
    let t_kind := (f3 ∘ (f2 ∘ f1)) tree in 
    let t_zip := BTree.zip tree t_kind  in
    BTree.map fst
              (fun x => match x with
                     | (v,false) => Normal v
                     | (v,true)  => Critical v
                     end)
              t_zip.   
  
  Definition serialization `(tree:BTree.t A B) (m:N) : list(segment A B) :=
    tree_to_segments (annotate tree m).

        
  Hint Unfold serialization annotate : tree.
  
  Lemma annotate_prop:
    forall A B v (l r:BTree.t A B) (m:N),
      annotate (Node v l r) m =
      Node (if is_critical m (1+size l+size r) (size l) (size r)
            then Critical v
            else Normal v)
           (annotate l m)
           (annotate r m).
  Proof.
    intros A B v l r m.
    unfold annotate.
    autounfold with sydpacc.
    assert (
        forall tree,
        mapt (fun _ : N => false) (fun (n : N) (l0 r0 : t N N) => is_critical m n (root l0) (root r0))
             (uAcc (fun arg : N * N * N => let (p, c) := arg in let (a, b) := p in a + b + c)
                   (map (fun _ : A => 1) (fun _ : B => 1) tree)) =
        Spec.mapt (fun _ : N => false) (fun (n : N) (l0 r0 : t N N) => is_critical m n (root l0) (root r0))
             (Spec.uAcc (fun arg : N * N * N => let (p, c) := arg in let (a, b) := p in a + b + c)
                        (Spec.map (fun _ : A => 1) (fun _ : B => 1) tree))
      ) as Heq by now (intro ; autorewrite with tree).
    repeat rewrite zip_eq
      with (H1 := eq_refl) (H2 := Heq _ ).
    repeat rewrite zip_eq
      with (H1 := eq_refl) (H2 := eq3 _ _ _ _).
    autorewrite with tree.
    set(num := is_critical m (1+size l+size r) (size l) (size r)).
    simpl. do 2 (f_equal; autorewrite with tree); apply spec_zip_pi.
  Qed.
  
End Serialization.

Section Deserialization.

  Fixpoint remove_annotation `(tree: BTree.t (node_type A B) B) : option (BTree.t A B) :=
    match tree with
    | Leaf(Normal v) => Some(Leaf v)
    | Node v l r =>
      match remove_annotation l with
      | None => None
      | Some l => match remove_annotation r with
                 | None => None
                 | Some r => Some(Node v l r)
                 end
      end
    | _ => None
    end.
                              
  Fixpoint rev_segment_to_trees `(l:segment A B) stack :
    list (BTree.t (node_type A B) B) :=
    match l with
    | [] => stack
    | (Le v)::l' => rev_segment_to_trees l' ((BTree.Leaf (Normal v))::stack)
    | (Cr v)::l' => rev_segment_to_trees l' ((BTree.Leaf (Critical v))::stack)
    | (No v)::l' =>
      match stack with
      | l::r::stack' =>
        rev_segment_to_trees l' ((BTree.Node v l r)::stack')
      | _ => []
      end
    end.

  Lemma rev_segment_to_trees_app:
    forall A B (seg : segment A B),
      wf_segment seg ->
      exists tree,
        forall l stack,
          rev_segment_to_trees (rev seg ++ l) stack =
          rev_segment_to_trees l (tree::stack).
  Proof.
    intros A B seg H. 
    induction H as [ v | v | l1 l2 v Hl1 IHl1 Hl2 IHl2 ]; simpl.
    - exists (Leaf(Normal v)). intros; trivial.
    - exists(Leaf(Critical v)). intros; trivial.
    - destruct IHl2 as [t2 H2].
      destruct IHl1 as [t1 H1].
      exists(Node v t1 t2).
      intros.
      rewrite rev_app_distr. repeat rewrite <- app_assoc.
      now rewrite H2, H1.
  Qed.
     
  Corollary rev_segment_to_trees_wf_singleton:
    forall A B (seg : segment A B),
      wf_segment seg ->
      exists tree,
        rev_segment_to_trees (rev seg) [] = [tree].
  Proof.
    intros A B seg H.
    destruct (rev_segment_to_trees_app H)
             as [tree Htree].
    exists tree.
    rewrite <- app_nil_r with (l:=rev seg).
    now apply Htree.
  Qed.
    
  Fixpoint graft `(tree: BTree.t (node_type A B) B) (stack:list(BTree.t A B)) :
    option( (BTree.t A B) * list(BTree.t A B) ):=
    match tree with
    | Leaf(Normal v) => Some (@BTree.Leaf A B v, stack)
    | Leaf(Critical v) =>
      match stack with
      | l::r::stack' => Some(BTree.Node v l r, stack')
      | _ => None
      end
    | Node v l r =>
      match graft l stack with
      | None => None
      | Some (l', stack') =>
        match graft r stack' with
        | None => None
        | Some(r', stack'') => 
          Some (BTree.Node v l' r', stack'')
        end
      end
    end.

  Definition segments_to_subtrees `(segs:list(segment A B)) : list(BTree.t (node_type A B) B) :=
    List.rev' (List.flat_map
                 (fun seg=>rev_segment_to_trees (List.rev' seg) [])
                 segs).

  Lemma segments_to_subtrees_app:
    forall A B (segs1 segs2:list(segment A B)),
      segments_to_subtrees (segs1++segs2) =
      segments_to_subtrees segs2 ++ segments_to_subtrees segs1.
  Proof.
    intros A B segs1 segs2.
   unfold segments_to_subtrees.
   unfold rev'. repeat rewrite rev_append_rev.
   repeat rewrite app_nil_r.
   rewrite flatmap_app.
   now rewrite rev_app_distr.
  Qed.
  
  Fixpoint rev_subtrees_to_trees `(l:list(BTree.t (node_type A B) B)) stack :
    list (BTree.t A B) :=
    match l with
    | [ ] => stack
    | tree::l' =>
      match remove_annotation tree with
      | None =>
        match graft tree stack with
        | None => [ ]
        | Some (tree',stack') =>
          rev_subtrees_to_trees l' (tree'::stack')
        end
      | Some tree' =>
        rev_subtrees_to_trees l' (tree'::stack)
      end
    end.

  Definition deserialization `(segs:list(segment A B)) : option (BTree.t A B) :=
    let stack := rev_subtrees_to_trees (segments_to_subtrees segs) [] in 
    match stack with
    | [ tree ] => Some tree
    | _ => None
    end.
    
End Deserialization.

Lemma serialization_not_empty:
  forall A B (tree: t A B) m,
    serialization tree m <> [].
Proof.
  intros A B tree m.
  intro H; induction tree as [ v | v tree3 IHtree1 tree4 IHtree2 ].
  - compute in H. inversion H.
  - unfold serialization in *.
    rewrite annotate_prop in H.
    rewrite <- spec_t2s_tree_to_segments in H, IHtree1, IHtree2.
    set(cond := is_critical m (1 + size tree3 + size tree4) (size tree3) (size tree4)) in *.
    destruct cond; simpl in H.
    + inversion H.
    + destruct(spec_t2s (annotate tree3 m)) eqn:HH; auto.
      destruct(spec_t2s (annotate tree4 m)) eqn:HHH; auto.
      inversion H.
Qed.


Lemma rev_subtrees_to_trees_serialization:
  forall (m:N) `(tree: BTree.t A B),
  exists tree',
    forall  l  stack,
    rev_subtrees_to_trees(segments_to_subtrees (serialization tree m) ++ l) stack =
    rev_subtrees_to_trees l (tree'::stack).
Proof.
Admitted.

Lemma deserialization_serialization_1:
  forall `(tree: BTree.t A B),
    deserialization(serialization tree 1) = Some tree.
Proof.
  intros A B tree.
  pose(Tree:=tree).
  induction tree as [ v | v l IHl r IHr ].
  - trivial.
  - unfold serialization.
    rewrite <- spec_t2s_tree_to_segments.
    rewrite annotate_prop.
    rewrite is_critical_1.
    simpl.
    repeat rewrite spec_t2s_tree_to_segments.
    replace (tree_to_segments(annotate l 1))
      with (serialization l 1) by auto.
    replace (tree_to_segments(annotate r 1))
      with (serialization r 1) by auto.
    unfold deserialization.
    replace ([Cr v] :: (serialization l 1) ++ (serialization r 1))
        with ([[@Cr A B v]] ++ (serialization l 1) ++ (serialization r 1))
        by auto.
    repeat rewrite segments_to_subtrees_app.
    replace (segments_to_subtrees [[Cr v]])
      with ([@Leaf _ B (@Critical A _ v)])
      by now compute.
    destruct(rev_subtrees_to_trees_serialization 1 r) as [tree_r Hr].
    destruct(rev_subtrees_to_trees_serialization 1 l) as [tree_l Hl].
    assert(tree_l = l).
    {
      assert(rev_subtrees_to_trees (segments_to_subtrees (serialization l 1)) [] = [ tree_l ]) as HH.
      {
        rewrite <- app_nil_r with (l:=segments_to_subtrees (serialization l 1)).
        rewrite Hl.
        trivial.
      }
      unfold deserialization in IHl.
      rewrite HH in IHl.
      now inversion IHl.
    }
    subst.
    assert(tree_r = r).
    {
      assert(rev_subtrees_to_trees (segments_to_subtrees (serialization r 1)) [] = [ tree_r ]) as HH.
      {
        rewrite <- app_nil_r with (l:=segments_to_subtrees (serialization r 1)).
        rewrite Hr.
        trivial.
      }
      unfold deserialization in IHr.
      rewrite HH in IHr.
      now inversion IHr.
    }
    subst.
    
    repeat rewrite <- app_assoc.
    rewrite Hr, Hl.
    now simpl.
Qed.
    
(** * Type Correspondence *)

Definition valid_tree `(tree: list(segment A B)) : bool :=
  is_some(deserialization tree).

Lemma valid_tree_iff:
  forall A B (t:list(segment A B)),
    valid_tree t = true -> deserialization t <> None.
Proof.
  unfold valid_tree, is_some.
  intros A B t H H'.
  destruct(deserialization t) eqn:H''; discriminate.
Qed.

Definition LTree A B := { segs:list(segment A B) | valid_tree segs = true }.

Lemma deserialization_exists:
  forall A B (ltree: LTree A B),
  exists tree, deserialization (`ltree) = Some tree.
Proof.
  intros A B ltree.
  destruct (deserialization (`ltree)) as [ tree | ] eqn:Htree.
  - exists tree; trivial.
  - destruct ltree as [ segs Hsegs] ; simpl in Htree.
    unfold valid_tree, is_some in Hsegs.
    rewrite Htree in Hsegs.
    discriminate.
Qed.

Lemma ltree_inj:
  forall A B (t1 t2: LTree A B),
    `t1 = `t2 -> t1 = t2.
Proof.
  intros A B [t1 H1] [t2 H2] H; simpl in *.
  subst.
  assert(H1 = H2) by apply UIP.Bool.UIP.
  now subst.
Qed.
  
Definition join A B (ltree: LTree A B): BTree.t A B :=
  let Hlt := valid_tree_iff (proj1_sig ltree) (proj2_sig ltree) in
  no_some (exist (fun l=>l<>None) (deserialization (proj1_sig ltree)) Hlt).
Arguments join [A B].

#[export] Program Instance surjective_join (A B:Type) : Surjective (@join A B).
Next Obligation.
  set(segs := serialization y 1).
  assert(H: deserialization segs = Some y) by
      (unfold segs; apply deserialization_serialization_1).
  assert(Hsegs: valid_tree segs = true)
    by (subst; unfold valid_tree; now rewrite H).
  set(lt := exist (fun l=>valid_tree l =true) segs Hsegs).
  exists lt.
  assert(HH: Some(join lt) = Some y).
  {
    unfold join. simpl (` lt). rewrite <- H.
    apply some_no_some.
  }
  now inversion HH.
Qed.

#[export] Program Instance ltree_btree_corr A B :
  TypeCorr (@join A B).

Section map.

  Definition map_local {A B C D} (kL: A -> C) (kN: B -> D) (seg: segment A B) :=
    let fmap (v:value A B) :=
        match v with
        | Le v => Le (kL v)
        | No v => No (kN v)
        | Cr v => Cr (kN v)
        end
    in map' fmap seg.

  Fixpoint map_subtree A B C D (kL:A->C)(kN:B->D) (st:BTree.t (node_type A B) B) :
    BTree.t (node_type C D) D :=
    match st with
    | Node v l r =>
      Node (kN v)
           (map_subtree kL kN l)
           (map_subtree kL kN r)
    | Leaf(Normal v) => Leaf (Normal (kL v))
    | Leaf(Critical v) => Leaf(Critical (kN v))
    end.

  Lemma rev_segment_to_trees_map_comm:
    forall A B C D (seg: segment A B) (kL:A->C) (kN:B->D) stack,
      rev_segment_to_trees ((map_local kL kN) seg)
                           (List.map (map_subtree kL kN) stack) =
      List.map (map_subtree kL kN)
               (rev_segment_to_trees seg stack).
  Proof.
    intros A B C D seg; induction seg as [ | seg segs IH ];
      intros kL kN stack.
    - trivial.
    - unfold map_local;
        rewrite map'_map; simpl; rewrite <- map'_map.
      destruct seg as [ v | v | v].
      + replace (Leaf(Normal(kL v))::List.map (map_subtree kL kN) stack)
          with  (List.map (map_subtree kL kN) ((Leaf(Normal v))::stack))
          by auto.
        now unfold map_local in IH; rewrite IH.
      + destruct stack as [ | stl [ | str stack' ]]; simpl; auto. 
        replace ((Node (kN v)
                       (map_subtree kL kN stl)
                       (map_subtree kL kN str))
                   :: List.map (map_subtree kL kN) stack')
          with  (List.map (map_subtree kL kN) ((Node v stl str)::stack'))
          by auto.
        now unfold map_local in IH; rewrite IH.
      + replace (Leaf(Critical(kN v))::List.map (map_subtree kL kN) stack)
          with  (List.map (map_subtree kL kN) ((Leaf(Critical v))::stack))
          by auto.
        now unfold map_local in IH; rewrite IH.
  Qed.

  
  Lemma segments_to_subtrees_map_comm:
    forall A B C D (segs: list(segment A B)) (kL:A->C) (kN:B->D),
      segments_to_subtrees (List.map (map_local kL kN) segs) =
      List.map (map_subtree kL kN) (segments_to_subtrees segs).
  Proof.
    intros A B C D segs. induction segs as [ | seg segs IH]; intros kL kN.
    - trivial.
    - unfold segments_to_subtrees in *.
      unfold rev' in *; repeat rewrite <- rev_alt.
      simpl. repeat rewrite rev_app_distr.
      repeat rewrite rev_alt, IH.
      repeat rewrite <- rev_alt.
      rewrite map_app. f_equal.
      set(HH:=rev_segment_to_trees_map_comm).
      specialize(HH _ _ _ _ (rev seg) kL kN []).
      simpl in HH.
      rewrite map_rev, <- HH.
      do 2 f_equal.
      unfold map_local. repeat rewrite map'_map.
      now rewrite map_rev.
  Qed.

  Lemma remove_annotation_map_comm:
    forall A B C D  (tree: t (node_type A B) B) (kL:A->C)(kN:B->D),
      remove_annotation (map_subtree kL kN tree) =
      match remove_annotation tree with
      | None => None
      | Some tree' => Some(BTree.map kL kN tree')
      end.
  Proof.
    intros A B C D tree; induction tree as [ [ v | v] | v l IHl r IHr];
      intros kL kN.
    - trivial.
    - trivial.
    - simpl. rewrite IHl, IHr.
      destruct(remove_annotation l);
        destruct(remove_annotation r); auto.
      now autorewrite with tree.
  Qed.

  Lemma graft_map_comm:
    forall A B C D  (tree: t (node_type A B) B) (kL:A->C)(kN:B->D) stack,
      graft (map_subtree kL kN tree) (List.map (map kL kN) stack) =
      match graft tree stack with
      | None => None
      | Some(tree', stack') =>
        Some(map kL kN tree', List.map (map kL kN) stack')
      end.
  Proof.
    intros A B C D tree; induction tree as [ [ v | v ] | v l IHl r IHr ]; intros kL kN stack.
    - trivial.
    - simpl.
      destruct stack as [ | t1 [ | t2 stack' ]].
      + trivial.
      + trivial.
      + simpl. now autorewrite with tree.
    - simpl.
      rewrite IHl. destruct(graft l stack); auto.
      destruct p as [ tree' stack' ].
      rewrite IHr. destruct(graft r stack'); auto.
      destruct p as [ tree'' stack'' ].
      now autorewrite with tree.
  Qed.
      
  Lemma rev_subtrees_to_trees_map_comm:
    forall A B C D  (subtrees: list (t (node_type A B) B)) (kL:A->C)(kN:B->D) stack,
      rev_subtrees_to_trees (List.map (map_subtree kL kN) subtrees)
                            (List.map (BTree.map kL kN) stack)  =
      List.map (BTree.map kL kN) (rev_subtrees_to_trees subtrees stack).
  Proof.
    intros A B C D subtrees;
      induction subtrees as [ | st subtrees IH ];
      intros kL kN stack.
    - trivial.
    - simpl.
      rewrite remove_annotation_map_comm.
      destruct (remove_annotation st) as [ ].
      + replace (map _ _ t :: _ _ stack)
          with (List.map (map kL kN) (t::stack))
          by auto.
        apply IH.
      + rewrite graft_map_comm.
        destruct(graft st stack).
        * destruct p as [tree' stack'].
          replace (map _ _ tree' :: _ _ stack')
            with (List.map (map kL kN) (tree'::stack'))
            by auto.
          apply IH.
        * trivial.
  Qed.
  
  Lemma deserialization_map_comm:
    forall A B C D (kL:A->C) (kN:B->D) lt,
      deserialization (List.map (map_local kL kN) lt) =
      match deserialization lt with
      | None => None
      | Some tree => Some (BTree.map kL kN tree)
      end.
  Proof.
    intros A B C D kL kN lt;
      unfold deserialization.
    replace [] with (List.map (BTree.map kL kN) []) by auto.
    rewrite segments_to_subtrees_map_comm.
    rewrite rev_subtrees_to_trees_map_comm.
    destruct(rev_subtrees_to_trees(segments_to_subtrees lt) []); auto.
    destruct l ; auto.
  Qed.
    
  Lemma valid_tree_map:
    forall A B C D (kL:A->C) (kN:B->D) segs,
      valid_tree segs = true ->
      valid_tree (List.map(map_local kL kN) segs) = true.
  Proof.
    intros A B C D kL kN segs H.
    unfold valid_tree, is_some in *.
    rewrite deserialization_map_comm.
    destruct(deserialization segs) eqn:H'.
    - trivial.
    - discriminate.
  Qed.
  
  Definition map A B C D (kL:A->C)(kN:B->D)(lt:LTree A B) : LTree C D.
    refine(exist _ (List.map (map_local kL kN) (proj1_sig lt)) _).
    destruct lt as [lt Hlt]; simpl.
    now rewrite valid_tree_map.
  Defined.
  Global Arguments map [A B C D].

  #[export] Instance map_tree_map_ltree {A B C D} (kL:A->C) (kN:B->D) :
    FunCorr (BTree.map kL kN) (map kL kN).
  Proof.
    constructor; intros [segs Hsegs]  _.
    unfold map, join; simpl.
    apply some_inj_eq.
    repeat rewrite some_no_some.
    rewrite deserialization_map_comm.
    destruct(deserialization segs) eqn:H' at 1.
    - do 2 f_equal.
      apply some_inj_eq.
      now rewrite some_no_some.
    - unfold valid_tree in Hsegs.
      contradict Hsegs.
      rewrite H'; simpl; auto.
  Qed.

End map.

Section reduce.

  Definition opL A B C
             (k: (A * B * A) -> A)
             (phi : B -> C)
             (psiL: (C * C * A) -> C)
             (psiR: (A * C * C) -> C)
             (a0 : option (list (sum A C) * option N)) (b: value A B) :=  
    match a0 with
    | None => None
    | Some (stack, d) =>
      match b with
      |  Le val => Some ((inl C val)::stack, incr d)
      |  Cr val => Some ((inr A (phi val)) :: stack, Some 0%N)
      |  No val =>
        match d with
        | Some 0%N =>
          match stack with
          | (inr _ lv)::(inl _ rv)::stacks => Some (inr A (psiL (lv,phi val,rv))::stacks, Some 0%N)
          | _ => None
          end
        | Some 1%N =>
          match stack with
          | (inl _ lv)::(inr _ rv)::stacks => Some (inr A (psiR (lv,phi val,rv))::stacks, Some 0%N)
          | _ => None
          end
        | _ =>
          match stack with
          | (inl _ lv)::(inl _ rv)::stacks => Some (inl C (k(lv, val,rv))::stacks, decr d)
          | _ => None
          end
        end                
      end
    end.
    

  Definition reduce_local {A B C}
             (k: (A * B * A) -> A)
             (phi : B -> C)
             (psiL: (C * C * A) -> C)
             (psiR: (A * C * C) -> C)
             (seg : segment A B) : option (sum A C) :=
    match fold_left (opL k phi psiL psiR) (rev' seg) (Some ([],None)) with
    | Some (h::t, _) => Some h
    | _ => None
    end.

  Definition opG A C (psiN : A * C * A -> A) (a0 : option (list A)) (b: sum A C) :=
    match b with 
    |  inl _ val =>
       match a0 with
       | Some a1 => Some (val::a1)
       | _ => None
       end
    | inr _ val =>
      match a0 with
      | Some (lv::rv::stacks) => Some (psiN (lv, val, rv)::stacks)
      | _ => None
      end
    end.
  
  Definition reduce_global (A C:Type)
             (psiN : A * C * A -> A)
             (gt : list(sum A C)) : option A (* TODO: the option is not very nice *) :=
    match fold_left (opG psiN) (rev' gt) (Some []) with
    | Some (a::_) => Some a
    | _ => None
    end.
  
  Definition reduce_segs (A B C:Type) (k: (A * B * A) -> A) 
             `{Hc : ClosureU A B C k phi psiN psiL psiR}
             (segs : list (segment A B)) : option A :=
    let gt := map_filter_some (reduce_local k phi psiL psiR) segs in
    reduce_global psiN gt.

  Arguments reduce_segs [A B C] k {phi psiN psiL psiR Hc}.

  Definition reduce {A B C} (k:(A*B*A)->A)
             `{H: ClosureU A B C k phi psiN psiL psiR } :
    LTree A B -> option A (* TODO: the option is not very nice *) :=
    (reduce_segs k) ∘ (@proj1_sig _ _).

  Global Arguments reduce [A B C] k {phi psiN psiL psiR H}.

  Lemma map_filter_some_app:
    forall A B (f:A->option B) l1 l2,
      map_filter_some f (l1++l2) =
      (map_filter_some f l1) ++ (map_filter_some f l2).
  Proof.
    intros A B f l1; induction l1 as [ | h1 t1 IH]; intro l2.
    - trivial.
    - simpl. rewrite IH.
      destruct(f h1); auto.
  Qed.
  
  Lemma reduce_btree_reduce:
    forall A B C (k:(A*B*A)->A) `{H: ClosureU A B C k phi psiN psiL psiR } segs,
      reduce_segs k segs =
      match deserialization segs with
      | None => None
      | Some tree => Some (BTree.reduce k tree)
      end.
  Proof.
    intros A B C k phi psiN psiL psiR H segs.
    unfold reduce_segs, reduce_local, reduce_global.
    induction segs as [ | seg segs IH] using rev_ind.
    - trivial.
    - unfold rev' in *. rewrite <- rev_alt in *.
      rewrite map_filter_some_app.
      rewrite rev_app_distr.
      rewrite fold_left_app. simpl.
  Admitted.

  #[export] Instance reduce_tree_reduce_ltree (A B C:Type) (k:(A*B*A)->A)
           `{H: ClosureU A B C k phi psiN psiL psiR } :
    FunCorr (Some ∘ (BTree.reduce k)) (reduce k).
  Proof.
    constructor. intros ltree _.
    unfold reduce, join; autounfold with sydpacc; simpl.
    destruct (deserialization_exists ltree) as [ tree Htree].
    match goal with
    | [ |- context C [ no_some ?T ] ] =>
      assert(no_some T = tree) as Heq
        by (apply some_inj_eq;
            now rewrite some_no_some)
    end. rewrite Heq.
    destruct ltree as [ segs Hsegs ]. simpl in *.
    rewrite reduce_btree_reduce.
    now rewrite Htree.
  Qed.

  Section reduce_proof.

    Inductive prop_no_critical (A B : Type) : segment A B -> Prop :=
    | no_crit_leaf : forall (v:A), prop_no_critical ([Le v])
    | no_crit_node : forall (v:B) (l r: segment A B),
        prop_no_critical l -> prop_no_critical r -> prop_no_critical ((No v) :: l ++ r).

    Inductive prop_has_critical (A B : Type) : segment A B -> Prop :=
    | has_crit_crit : forall (v:B), prop_has_critical [Cr v]
    | has_crit_node_left : forall (v:B) (l r: segment A B), prop_has_critical l  -> prop_no_critical r ->
                                                       prop_has_critical ((No v) :: l ++ r)
    | has_crit_node_right : forall (v:B) (l r: segment A B), prop_no_critical l -> prop_has_critical r ->
                                                        prop_has_critical ((No v) :: l ++ r).


    (*
    Check reduce_local.
    Lemma reduce_local_no_crit :
      forall (A B : Type) (k:A * B * A -> A) `{H: ClosureU A B C k phi psiN psiL psiR }
        (seg : segment A B) (res_local : A),
        prop_no_critical seg -> reduce_local seg  = Some (res_local, d) -> d = None.
*)
        
    Lemma reduce_tree_reduce_ltree_segL :
      forall (A B : Type) (k:A * B * A -> A) `{H: ClosureU A B C k phi psiN psiL psiR }
        (t : BTree.t A B) (seg : segment A B),
        deserialization ([seg]) = Some t -> prop_no_critical seg -> 
        reduce_segs k [seg]  = Some (BTree.reduce k t).
    Proof.
      intros.
      destruct H1.
      - unfold deserialization in H0. simpl in H0.
        assert (t = Leaf v).
        { apply some_inj_eq in H0. symmetry; assumption. }
        rewrite H1. unfold reduce_segs.
        simpl. unfold reduce_global; simpl.
        unfold BTree.reduce. simpl.
        reflexivity.
      - admit.    
    Admitted.

    Lemma  reduce_tree_reduce_ltree_segN_crit_left :
      forall (A B C:Type) (k:A * B * A -> A) `{H: ClosureU A B C k phi psiN psiL psiR }
        (t : BTree.t A B) (segL segR : segment A B)  (x y l: A) (r b: B) (lt: segment A B),
        prop_no_critical segL -> prop_no_critical segR ->
        prop_no_critical lt ->
        reduce_local k phi psiL psiR segL = Some (inl x) ->
        reduce_local k phi psiL psiR segR = Some (inl y) ->
        deserialization ([[No b] ++ lt ++ [Cr r] ; segL; segR]) = Some t -> 
        reduce_segs k  [[No b] ++ lt ++ [Cr r] ; segL; segR] = Some (BTree.reduce k t).
    Proof.
      intros A B C k phi psiN psiL psiR H t segL segR x y l r b lt.
      intros H_no_crit_l H_no_crit_r H_no_crit_lt H_red_l H_red_r H_des_t. 
      unfold reduce_segs. unfold map_filter_some.
      rewrite -> H_red_l;  rewrite -> H_red_r.
      unfold reduce_local.
      unfold rev'; simpl.
      unfold rev_append.
      destruct H_no_crit_lt.
      + simpl. unfold reduce_global; simpl.
        rewrite <- some_inj_eq.
        destruct H.
        destruct closed_u. destruct H0.
        assert (close_1 : (psiN (x, psiR (v, phi b, phi r), y)) = (psiN(v,phi b,psiN(x,phi r,y))))
          by (symmetry; apply H1).
        unfold deserialization in H_des_t; simpl in H_des_t.
        replace ([[No b; Le v; Cr r]; segL; segR]) with ( [[No b; Le v; Cr r]] ++ [segL] ++ [segR]) in H_des_t.
        repeat rewrite segments_to_subtrees_app in H_des_t.
        unfold segments_to_subtrees in H_des_t. simpl in H_des_t.
        admit.
        ++ admit.
      + admit.
    Admitted.        
        
     End reduce_proof.
End reduce.


Close Scope sydpacc_scope.
Close Scope N_scope.
