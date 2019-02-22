Require Import Coq.Lists.List Omega NArith. Import ListNotations.
From SyDPaCC.Support.NLists Require Import NLength NNth NFirstSkip.

Open Scope N_scope.

Fixpoint scanl (A B:Type)(op:A->B->A)(identity:A)(l:list B) : list A := 
  identity::
          match l with 
            | []   => []
            | h::t => scanl A B op (op identity h) t
          end.

Arguments scanl [A B].

Lemma scanl_length:
  forall (A B:Type)(op:A->B->A)(identity:A)(l:list B),
    length (scanl op identity l) = 1 + length l.
Proof.  
  intros A B op identity l; generalize dependent identity; induction l.
  intros; trivial. 
  intros; simpl; rewrite IHl; simpl; trivial.
Qed.

Arguments scanl_length [A B].

Hint Rewrite scanl_length : length.

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
    zify; omega.
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

Fixpoint scan {A B:Type}(op:A->B->A)(identity:A)(l:list B) : list A := 
  match l with 
    | []   => []
    | h::t =>let id := (op identity h) in id::scan op id t
  end.

Lemma scan_length:
  forall (A B : Type)(op:A->B->A)(identity:A)(l:list B),
    length (scan op identity l) = length l.
Proof.  
  intros A B op identity l; generalize dependent identity; induction l as [ | a l IHl ].
  - intros; trivial. 
  - intros; simpl; rewrite IHl; simpl; trivial.
Qed.

Hint Rewrite scan_length : length.

Lemma scan_fold:
  forall (A B:Type)(op:A->B->A)(identity:A)(l:list B)(default:A) (index:N), 
    index < length l ->
    nth index (scan op identity l) default = 
    List.fold_left op (firstn (1+index) l) identity.
Proof.
  intros A B op identity l default index validIndex; 
    generalize dependent identity; generalize dependent index; induction l.
  - intros; rewrite firstn_nil; simpl in *; destruct index; trivial;
    zify; omega.
  - intros index validIndex identity; destruct index.
    + simpl; rewrite firstn_equation; trivial.
    + rewrite firstn_equation.
      destruct(1 + N.pos p) eqn:Heq.
      * zify; omega.
      * simpl; rewrite IHl.
        -- repeat f_equal. repeat rewrite N.pos_pred_spec; rewrite <- Heq.
           rewrite N.add_pred_r; auto; zify; omega.
        -- rewrite N.pos_pred_spec. rewrite length_cons in validIndex.
           apply N.pred_lt_mono in validIndex; trivial.
           rewrite N.add_1_l in validIndex.
           now rewrite N.pred_succ in  validIndex.
           clear; intro H; zify; omega.
Qed.

(*
Fixpoint scanLast {A B:Type}(op:A->B->A)(identity:A)(l:list B) : list A * A := 
  match l with 
    | []   => ([], identity)
    | h::t =>let id := (op identity h) in 
               let result := scanLast op id t in
                 (id::fst result, snd result)
  end.

Lemma scanLastFst:
  forall (A B:Type)(op:A->B->A)(identity:A)(l:list B),
    fst (scanLast op identity l) = scan op identity l.
Proof.
  intros A B op identity l. 
  generalize dependent identity.
  induction l as [|x xs IH].
  - trivial.
  - intro e; simpl; rewrite IH; trivial.
Qed.

Lemma scanLastSnd:
  forall (A B:Type)(op:A->B->A)(identity:A)(l:list B),
    snd (scanLast op identity l) = List.fold_left op l identity.
Proof.
  intros A B op identity l.
  generalize dependent identity.
  induction l as [|x xs IH].
  - trivial.
  - intro e. simpl. rewrite IH. trivial.
Qed.

*)