Require Import NArith Omega Coq.Lists.List Program Classes.EquivDec.
Import ListNotations.

From SyDPaCC.Support Require Import UIP List Sig NList.
Require Import SyDPaCC.Bsml.Model.Core.


Set Implicit Arguments.

(** * Properties of Processor Identifiers *)

Module Make(Bsp : BSP_PARAMETERS).

  Notation "x <? y":=( N.ltb x y = true ). 

  Local Notation pid := { n : N | n <? Bsp.p }.

  Ltac pid :=
    simpl in *;
    assert (0 < Bsp.p) by apply Bsp.p_spec;
    repeat 
      match goal with
        | [ H: _ <? _ |- _ ] => apply N.ltb_lt in H
        | [ H: N.ltb _ _ = true |- _ ] => apply N.ltb_lt in H
        | [ |- N.ltb _ _ = true ] => apply N.ltb_lt
        | _ => try apply N.lt_pred_l; try apply N.pred_succ;
              try apply N.succ_pred;
              autorewrite with length in *; auto with arith pid;
              try (zify;omega)
      end.

  Notation processor := { n:N | n < Bsp.p }.

  Lemma proj1_sig_inj:
    forall i i': pid, proj1_sig i = proj1_sig i' -> i = i'.
  Proof.
    intros [i Hi] [i' Hi'] H; simpl in *; subst.
    assert(Hi = Hi') by (apply Bool.UIP).
    now f_equal.
  Qed.

  Hint Resolve proj1_sig_inj : pid.

  Lemma pid_dec: forall (i j : pid), { i=j } + { ~ i=j }.
  Proof. 
    intros [i Hi] [j Hj]. 
    case_eq(N.eq_dec i j); intros H _. 
    - left; now apply proj1_sig_inj.
    - right; contradict H; now inversion H.
  Qed.

  Program Instance pid_eq_dec : EqDec pid Logic.eq := pid_dec.
  
  Fact of_pid_aux (i:pid) : (proj1_sig i) < Bsp.p.
    destruct i; pid.
  Qed.
  
  Definition of_pid (i:pid) : processor :=
    exist (fun n=>n<Bsp.p) (proj1_sig i) (of_pid_aux i).

  Fact to_pid_aux (i:processor) : (proj1_sig i) <? Bsp.p.
    destruct i; pid.
  Qed.
  
  Program Definition to_pid (i:processor) : pid :=
    exist (fun n=>N.ltb n Bsp.p=true) (proj1_sig i) (to_pid_aux i).

  Definition to_N (i:pid) : N := proj1_sig i.

  Definition of_N {n:N}  (H:n<?Bsp.p) : pid :=
    exist _ n H.

  Fact of_N'_aux {n:N} (H:n<Bsp.p) : n <? Bsp.p.
    pid.
  Qed.
  
  Definition of_N' {n:N} (H:n<Bsp.p) : pid :=
    exist (fun n=>n<?Bsp.p) n (of_N'_aux H).

  Program Definition pids : list pid := 
    Sig.map (seq 0 Bsp.p) _.
  Next Obligation.
    induction Bsp.p as [ | p IH ] using N.peano_ind.
    - rewrite seq_equation in H. contradiction.
    - rewrite seq_S_app in H.
      apply in_app_or in H.
      destruct H as [H|H].
      + specialize (IH H). pid. 
      + simpl in H; destruct H; subst; pid.
  Qed.

  Hint Unfold to_N of_N of_N' pids : pid.

  Lemma pids_spec : forall (i:pid), In i pids.
  Proof.
    autounfold with pid. intros [i Hi].
    assert(i<Bsp.p) by pid. 
    assert(In i (seq 0 Bsp.p))
      by (apply in_seq; pid).
    assert(0 <= i < Bsp.p) by pid.
    assert(forall a a' : pid, ` a = ` a' -> a = a')
      by apply proj1_sig_inj.
    now apply Sig.in_in_map. 
  Qed.
  
  Hint Resolve pids_spec : pid.
  
  Fact pids_seq :
    List.map to_N pids = seq 0 Bsp.p.
    apply Sig.map_proj1_sig.
  Qed.
  
  Fact pids_length : length pids = Bsp.p.
    unfold pids; now autorewrite with length.
  Qed.

  Fact NoDup_pids : NoDup pids.
    apply NoDup_map_inv with (f:=to_N).
    rewrite pids_seq.
    rewrite seq_seq.
    apply NoDup_map.
    - intros x y H.
      zify; omega.
    - apply seq_NoDup.
  Qed.

  Hint Resolve NoDup_pids : pid.

  Hint Rewrite pids_length : length.

  Hint Resolve Bsp.p_spec : pid.

  Fact last_aux: N.pred Bsp.p <? Bsp.p.
    pid. 
  Qed.
  
  Definition last : pid :=
    exist (fun n=>n<?Bsp.p) (N.pred Bsp.p) last_aux.

  Fact first_aux : 0 <? Bsp.p. pid. Qed.
  
  Definition first : pid :=
    exist (fun n=>n<?Bsp.p) 0 first_aux.

  Fact of_mod_aux (n:N) : n mod Bsp.p <? Bsp.p.
    pid; apply N.mod_bound_pos; pid.
  Qed.
  
  Definition of_mod (n:N) : pid :=
    exist (fun n=>n<?Bsp.p) (n mod Bsp.p) (of_mod_aux n).

  Fact lt_bsp_p : forall (i:pid),  proj1_sig i < Bsp.p.
    intros [i Hi]; pid.
  Qed.

  Hint Resolve lt_bsp_p N.succ_pred_pos : pid.

  Lemma S_last : N.succ(proj1_sig last) = Bsp.p.
    pid.
  Qed.

  Hint Resolve S_last : pid.

  Fact lt_cong :
    forall(n m n' m':N), n=n' -> m=m' ->
                           (n < m <-> n' < m').
    intros; split; congruence.
  Qed.

  Fact nth_pids_aux :
    forall a : N,
      (fun n : N => n <? Bsp.p) a <-> (fun pos : N => pos < length pids) a.
    intro; split; intro; pid.
  Qed.

  Lemma nth_pids :
    forall (i:pid), Sig.nth pids (Sig.cast_sig i nth_pids_aux) = i.
  Proof.
    intros [i Hi].
    autounfold with pid. 
    rewrite Sig.map_nth by (intros; apply Bool.UIP).
    apply proj1_sig_inj; simpl.
    rewrite Sig.nth_spec with (default:= Bsp.p).
    simpl.
    rewrite seq_seq.
    rewrite <- (Nnat.N2Nat.id Bsp.p).
    rewrite map_nth.
    rewrite seq_nth; pid.
  Qed.

  Fact pids_cons : pids = first::List.tl pids.
    autounfold with pid.
    assert(forall A (l l':list A) P,  l = l' ->
              (forall a:A, In a l -> P a) ->
              forall a:A, In a l' -> P a)
      as H' by (intros;subst;auto).
    assert(seq 0 Bsp.p = seq 0 (N.succ (proj1_sig last)))
      by (rewrite S_last; trivial).
    assert(forall i, In i (seq 0 (N.succ (`last))) -> i <? Bsp.p) as HIn
        by now apply (H' _ _ _ _ H pids_obligation_1).
    replace (Sig.map (seq 0 Bsp.p) _)
        with (Sig.map (P:=fun n=>n <? Bsp.p) (seq 0 (N.succ (proj1_sig last)))
                      HIn)
      by (apply Sig.map_pi;pid).
    revert HIn.
    pattern(seq 0 (N.succ(` last))).
    rewrite seq_equation.
    rewrite <- N.succ_pos_spec.
    intro HIn; simpl; f_equal.
    now apply proj1_sig_inj.
  Qed.

  Fact split_pids :
    forall i:pid,
    exists pids_l pids_r, pids = pids_l ++ i :: pids_r.
    intro;  apply In_split, pids_spec.
  Qed.

  Fact split_pids_length :
    forall pids_l pids_r i,
    pids = pids_l ++ i :: pids_r ->
    length pids_l + length pids_r + 1 = Bsp.p.
    intros pids_l pids_r i H.
    rewrite <- pids_length, H.
    autorewrite with length.
    zify; omega.
  Qed.

  Lemma map_inj:
    forall A B (f:A->B) (H:forall a a', f a = f a' -> a = a') l l',
      map f l = map f l' -> l = l'.
  Proof.
    intros A B f Hf; induction l as [ | x xs IH]; intros l' Hmap.
    - destruct l'; simpl in *; trivial; discriminate.
    - destruct l'; simpl in *; try discriminate.
      inversion Hmap; subst; f_equal.
      + now apply Hf.
      + now apply IH.
  Qed.

  Fact succ_aux :
    forall i, i<>last -> N.succ (` i) <? Bsp.p.
  Proof.
    intros i H.
    assert((` i)<>N.pred Bsp.p) as H0
        by (contradict H; now apply proj1_sig_inj).
    clear H; destruct i; simpl in *; pid.
  Admitted.
  
  Definition succ (i : pid) (H:i<>last) : pid :=
    exist (fun n=>n<?Bsp.p) (N.succ (` i)) (succ_aux H).

  Fact pred_aux :
    forall i : pid,  N.pred (`i) <? Bsp.p.
    intros [ i Hi ]; pid.
    now apply N.lt_lt_pred.
  Qed.
  
  Definition pred (i : pid) : pid :=
    exist (fun n=>n<?Bsp.p) (N.pred (` i)) (pred_aux i).

  Proposition pid_ind (P:pid->Prop) :
    P first ->
    (forall (i:pid)(H:i<>last), P i -> P (succ H)) ->
    forall i, P i.
  Proof.
    intros H0 HS i; destruct i as [n HSn]; induction n as [ | n IH] using N.peano_ind.
    - match goal with [ |- P ?i' ] =>
                      assert(i' = first) as H by pid;
                        now rewrite H
      end.
    - assert(n<?Bsp.p) as Hn by pid.
      pose(i :=exist (fun n=>n<?Bsp.p) n Hn).
      assert(i<>last) as H.
      {
        intro H; apply f_equal with (f:=to_N) in H;
        unfold to_N, last in H; simpl in H;
          clear i IH P H0 HS; pid.
        rewrite N.add_1_l in HSn.
        rewrite H in HSn.
        rewrite N.succ_pred in HSn by (zify;omega).
        zify; omega.
      }
      assert(P i) by apply IH.
      match goal with
          [ |- P ?i' ] =>
          assert(i' = succ H) as H' by pid; rewrite H'
      end.
      now apply HS.
  Qed.

  Definition succ' (i:pid) : pid :=
    match pid_dec i last with
      | left _ => last
      | right H => succ H
    end.

  Fact succ_succ' :
    forall (i:pid)(H:i<>last),
      succ H = succ' i. 
  Proof.
    intros i H'; unfold succ'.
    destruct(pid_dec i last); try contradiction.
    now (apply proj1_sig_inj; simpl).
  Qed.

  Lemma H_succ_succ':
    forall (P:pid->Prop),
      (forall i, P i -> P (succ' i)) ->
      (forall i (H:i<>last),P i->P (succ H)).
  Proof.
    intros P HS i Hlast Hi.
    case_eq(pid_dec i last); intros Heq _ .
    - contradiction.
    - rewrite succ_succ'.
      now apply HS.
  Qed.
  
  Proposition pid_ind' (P:pid->Prop) :
    P first ->
    (forall (i:pid), P i -> P (succ' i)) ->
    forall i, P i.
  Proof.
    intros H0 HS i.
    assert(forall i (H:i<>last),P i->P (succ H))
      by (intros;now apply H_succ_succ').
    now apply pid_ind.
  Qed.
  
  Fact pid_up_to_aux (i:pid) :
    forall i',  In i' (seq 0 (N.succ(` i))) ->
                i' <? Bsp.p.
    intros a H; apply in_seq in H; destruct i; pid.
  Qed.
  
  Definition pid_up_to (i:pid) : list pid :=
    Sig.map (P:=fun n=>n<?Bsp.p) (seq 0 (N.succ (` i))) (pid_up_to_aux i).
  
  Fact pid_up_to_last:
    pids = pid_up_to last.
    unfold pid_up_to; autounfold with pid.
    assert( forall a a' : pid, ` a = ` a' -> a = a') by pid.
    assert(  seq 0 Bsp.p = seq 0 (N.succ(` last)) ) by (now rewrite S_last).
    now apply Sig.map_pi.
  Qed.
    
  Proposition pids_ind (P: list pid->Prop) :
    P [ first ] ->
    (forall (i:pid)(H:i<>last), P (pid_up_to i) -> P (pid_up_to (succ H))) ->
    P pids.
  Proof.
    intros H H0.
    rewrite pid_up_to_last.
    apply pid_ind with (P:=fun i=>P (pid_up_to i)).
    - unfold pid_up_to.
      assert(forall i, In i [ 0 ] -> i <? Bsp.p) as Hin
          by (simpl; intros i Hi;
              destruct Hi as [ Hi | Hi ]; subst; intuition; pid).
      rewrite Sig.map_pi with (l':=[ 0 ])(H':=Hin).
      + assert(Sig.map [0] Hin = [ first ]) as Heq
            by (simpl; f_equal; apply proj1_sig_inj; now simpl).
        now rewrite Heq.
      + apply proj1_sig_inj.
      + rewrite seq_S_app; simpl.
        now rewrite seq_equation.
    - auto.
  Qed.

  Proposition pids_ind' (P: list pid->Prop) :
    P [ first ] ->
    (forall (i:pid), P (pid_up_to i) -> P (pid_up_to (succ' i))) ->
    P pids.
  Proof.
    intros H0 HS.
    assert(forall i (H:i<>last),P (pid_up_to i)->P (pid_up_to (succ H)))
      by (intros;now apply H_succ_succ').
    now apply pids_ind.
  Qed.

  Lemma pid_up_to_succ :
    forall (i:pid) (Hi:i<>last),
      pid_up_to (succ Hi) = (pid_up_to i) ++ [succ Hi].
  Proof.
    intros i Hi; unfold pid_up_to.
    assert(forall i', In i' (seq 0 (N.succ(` i)) ++ [N.succ (` i)]) -> i' <? Bsp.p) as Hi'.
    {
      intros i' Hi'. apply in_app_or in Hi'. destruct Hi' as [Hi' | Hi'].
      - eapply pid_up_to_aux; eauto.
      - assert(i' = N.succ (` i)) by pid. subst.
        now apply succ_aux in Hi. 
    }
    assert(  Sig.map (seq 0 (N.succ (` i))) (pid_up_to_aux i) ++ [succ Hi] =
            Sig.map (seq 0 (N.succ (` i)) ++ [N.succ (` i)]) Hi' ) as Heq.
    {
      repeat rewrite Sig.map_app by apply proj1_sig_inj. f_equal.
      - auto using Sig.map_pi, proj1_sig_inj.
      - simpl; f_equal. now apply proj1_sig_inj.
    }
    rewrite Heq. apply Sig.map_pi. apply proj1_sig_inj.
    apply seq_S_app.
  Qed.

  Ltac destruct_pids i :=
    let pids_l := fresh "pids_l" in
    let pids_r := fresh "pids_r" in
    let H := fresh "Hpids" in
    destruct (split_pids i) as [pids_l [pids_r H]];
      try rewrite H.
   
End Make.
      
Module Type TYPE (Bsp : BSP_PARAMETERS).
  Include Make Bsp.
End TYPE.