Require Import Coq.Lists.List NArith. Import ListNotations.
From SyDPaCC.Support.NLists 
Require Export NLength NSeq NNth NFirstSkip NScan.
Require Import SyDPaCC.Support.Sig.

Fixpoint mapi_aux {A B:Type} (f:N -> A -> B) (l:list A) (i:N): list B := 
  match l with 
    | nil => nil 
    | cons x xs => cons (f i x) (mapi_aux f xs (i+1))
  end.

Definition mapi  {A B:Type} (f:N -> A -> B) (l:list A) : list B := 
  mapi_aux f l 0.

Lemma length_mapi_aux: 
  forall {A B:Type} (f:N -> A -> B)(l:list A)(i:N),
    length(mapi_aux f l i) = length l.
Proof.
  induction l.
  - trivial.
  - simpl. intro i. rewrite IHl. trivial.
Qed.

Hint Rewrite @length_mapi_aux : length.

Lemma length_mapi: 
  forall {A B:Type} (f:N -> A -> B)(l:list A),
    length(mapi f l) = length l.
Proof.
  unfold mapi. 
  intros.
  apply length_mapi_aux.
Qed.

Hint Rewrite @length_mapi : length.

Lemma mapi_app:
  forall {A B:Type} (f:N -> A -> B) (l l':list A)(i:N),
    mapi_aux f (l++l') i = 
    (mapi_aux f l i) ++ (mapi_aux f l' 
                                (i+NLength.length l)).
Proof.
  induction l; intros l' i.
  - simpl. rewrite Nplus_0_r. trivial.
  - Opaque N.add. simpl. rewrite IHl. rewrite N.add_assoc. trivial.
Qed.
    
Require Import Omega.

Lemma mapi_aux_nth:
  forall (A B: Type)(f: N->A->B)(l:list A)(position first:N)(default:A),
  nth position (mapi_aux f l first) (f ((first+position)%N) default) =  
  f ((first+position)%N) (nth position l default).
Proof.
  intros A B f; induction l; intros position first default.
  - destruct position using N.peano_ind.
    + rewrite N.add_0_r. trivial.
    + trivial.
  - destruct position using N.peano_ind.
    + rewrite N.add_0_r. trivial.
    + simpl mapi_aux.
      rewrite nth_equation.
      destruct (N.succ position) eqn:Hpos.
      * apply N.succ_0_discr in Hpos.
        now exfalso.
      * rewrite <- Hpos; rewrite nth_equation with (pos:=N.succ position).
        rewrite Hpos, <- Hpos, N.pred_succ.
        replace (first + N.succ position)%N with ( (first + 1) + position)%N
          by (zify; omega).
        now rewrite IHl.
Qed.

Lemma mapi_nth:
  forall (A B: Type)(f: N->A->B)(l:list A)(position:N)(default:A),
  nth position (mapi f l) (f position default) =  
  f position (nth position l default).
Proof.
  unfold mapi.
  intros A B f l position default.
  rewrite mapi_aux_nth.
  trivial.
Qed.

Lemma map_length:
  forall {A:Type}{P:A->Prop}(l:list A) (H:forall a,In a l->P a),
    length(Sig.map l H) = length l.
Proof.
  induction l as [|x xs IH]; intro H.
  - auto.
  - simpl; rewrite IH; auto.
Qed.

Hint Rewrite @map_length : length.
