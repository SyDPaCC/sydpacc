Require Import Coq.Lists.List. Import ListNotations.
Require Recdef.
Require Import Arith NArith NPeano Omega.
From SyDPaCC.Support Require Import NLists.NLength Lists.Seq.

(* * Creating sequence of natural numbers of type [N]. *)

Open Scope N_scope.

(** [seq] takes number of type [N] and returns a list of numbers of type [N]. *)
Function seq (first:N)(size:N) { wf N.lt size } : list N := 
  match size with 
    | 0 => [] 
    | N => first::(seq (N.succ first) (N.pred size))
  end.
Proof.
  intros first size p teq; subst; apply N.lt_pred_l; zify; omega.
  apply N.lt_wf_0.
Qed.

Lemma seq_S_app:
  forall (first size :N),
    seq first (N.succ size) = ( seq first size ) ++ [ first + size ].
Proof.
  intros first size; generalize dependent first; 
  induction size using N.peano_ind; intro first.
  + do 3 (rewrite seq_equation; simpl); rewrite N.add_0_r; trivial.
  + rewrite seq_equation; simpl; destruct size; simpl.
    * do 4 (rewrite seq_equation; simpl).
      rewrite N.add_1_r; trivial.
    * rewrite Pos.pred_N_succ, IHsize.
      replace (Npos(Pos.succ p)) with (N.succ (Npos p)); auto.
      rewrite seq_equation with (size:=N.succ (Npos p)); simpl.
      rewrite Pos.pred_N_succ.
      do 3 f_equal. zify. omega.
Qed.

Lemma seq_seq:
  forall (first size :N),
    seq first size = 
        List.map N.of_nat (List.seq (N.to_nat first) (N.to_nat size)).
Proof.
  intros first size; generalize dependent first; 
  induction size using N.peano_ind; intro first; simpl.
  + apply seq_equation.
  + rewrite N2Nat.inj_succ. rewrite seq_S_app; simpl.
    replace(S(N.to_nat first)) with (N.to_nat(N.succ first))
      by now rewrite <- N2Nat.inj_succ.
    rewrite <- IHsize. 
    rewrite seq_equation; destruct size; simpl.
    * rewrite seq_equation; f_equal; zify; omega.
    * rewrite N2Nat.id; f_equal.
      replace (first+N.pos p) with (N.succ first + Pos.pred_N p).
      rewrite <- seq_S_app.
      now rewrite N.succ_pos_pred.
      replace (N.succ first) with (1 + first) by (zify; omega).
      rewrite <- N.succ_pos_pred with (p:=p).
      zify; omega.
Qed.

Lemma seq_length:
  forall (first size: N), 
    length(seq first size) = size.
Proof.
  intros first size; generalize dependent first;
  induction size using N.peano_ind; intro first; rewrite seq_equation.
  - trivial.
  - destruct size. 
    + simpl; rewrite seq_equation; auto with arith.
    + simpl. rewrite Pos.pred_N_succ, IHsize. destruct p; trivial.
Qed.

Hint Rewrite seq_length : length.

Lemma in_seq len start n :
  In n (seq start len) <-> start <= n < start+len.
Proof.
  rewrite seq_seq; split; intro H.
  - apply in_map_iff in H.
    destruct H as [ m [ H Hin] ].
    rewrite in_seq in Hin.
    zify; omega.
  - apply in_map_iff.
    exists (N.to_nat n).
    split.
    + apply N2Nat.id.
    + apply in_seq; zify; omega.
Qed.
           
Close Scope N_scope.