From SyDPaCC.Support Require Import UIP List Sig NList.
Require Import NArith Coq.Lists.List Program Classes.EquivDec Lia.
Import ListNotations.
Require Import SyDPaCC.Bsml.Model.Core.


Set Implicit Arguments.

(** * Properties of Processor Identifiers *)

Module Make(Bsp : BSP_PARAMETERS).

  Notation "x <? y":=( N.ltb x y = true ). 

  Local Notation pid := { n : N | n <? Bsp.p }.

  Definition ltb (x y : pid) := N.ltb (` x) (` y).
  #[export] Hint Unfold ltb : pid.

  Definition lt (x y : pid) := N.lt (` x) (` y).
  #[export] Hint Unfold lt : pid.

  Definition le (x y : pid) := N.le (` x) (` y).
  #[export] Hint Unfold le : pid.
  
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
            try lia
      end.

  Notation processor := { n:N | n < Bsp.p }.

  Lemma proj1_sig_inj:
    forall i i': pid, proj1_sig i = proj1_sig i' -> i = i'.
  Proof.
    intros [i Hi] [i' Hi'] H; simpl in *; subst.
    assert(Hi = Hi') by (apply Bool.UIP).
    now f_equal.
  Qed.

  #[export] Hint Resolve proj1_sig_inj : pid.

  Lemma pid_dec: forall (i j : pid), { i=j } + { ~ i=j }.
  Proof. 
    intros [i Hi] [j Hj]. 
    case_eq(N.eq_dec i j); intros H _. 
    - left; now apply proj1_sig_inj.
    - right; contradict H; now inversion H.
  Qed.

  #[export] Program Instance pid_eq_dec : EqDec pid Logic.eq := pid_dec.
  
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
    Sig.map (NList.seq 0 Bsp.p) _.
  Next Obligation.
    induction Bsp.p as [ | p IH ] using N.peano_ind.
    - rewrite seq_equation in H. contradiction.
    - rewrite seq_S_app in H.
      apply in_app_or in H.
      destruct H as [H|H].
      + specialize (IH H). pid. 
      + simpl in H; destruct H; subst; pid.
  Qed.

  #[export] Hint Unfold to_N of_N of_N' pids : pid.

  Lemma pids_spec : forall (i:pid), In i pids.
  Proof.
    autounfold with pid. intros [i Hi].
    assert(i<Bsp.p) by pid. 
    assert(In i (NList.seq 0 Bsp.p))
      by (apply In_seq; pid).
    assert(0 <= i < Bsp.p) by pid.
    assert(forall a a' : pid, ` a = ` a' -> a = a')
      by apply proj1_sig_inj.
    now apply Sig.in_in_map. 
  Qed.
  
  #[export] Hint Resolve pids_spec : pid.
  
  Fact pids_seq :
    List.map to_N pids = NList.seq 0 Bsp.p.
    apply Sig.map_proj1_sig.
  Qed.
  
  Fact pids_length : NList.length pids = Bsp.p.
    unfold pids; now autorewrite with length.
  Qed.

  Fact NoDup_pids : NoDup pids.
    apply NoDup_map_inv with (f:=to_N).
    rewrite pids_seq.
    rewrite seq_seq.
    apply NoDup_map.
    - intros x y H.
      lia.
    - apply seq_NoDup.
  Qed.

  #[export] Hint Resolve NoDup_pids : pid.

  #[export] Hint Rewrite pids_length : length.

  #[export] Hint Resolve Bsp.p_spec : pid.

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

  #[export] Hint Resolve lt_bsp_p N.succ_pred_pos : pid.

  Lemma S_last : N.succ(proj1_sig last) = Bsp.p.
    pid.
  Qed.

  #[export] Hint Resolve S_last : pid.

  Fact lt_cong :
    forall(n m n' m':N), n=n' -> m=m' ->
                           (n < m <-> n' < m').
    intros; split; congruence.
  Qed.

  Fact nth_pids_aux :
    forall a : N,
      (fun n : N => n <? Bsp.p) a <-> (fun pos : N => pos < NList.length pids) a.
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
    assert(NList.seq 0 Bsp.p = NList.seq 0 (N.succ (proj1_sig last)))
      by (rewrite S_last; trivial).
    assert(forall i, In i (NList.seq 0 (N.succ (`last))) -> i <? Bsp.p) as HIn
        by now apply (H' _ _ _ _ H pids_obligation_1).
    replace (Sig.map (NList.seq 0 Bsp.p) _)
        with (Sig.map (P:=fun n=>n <? Bsp.p) (NList.seq 0 (N.succ (proj1_sig last)))
                      HIn)
      by (apply Sig.map_pi;pid).
    revert HIn.
    pattern(NList.seq 0 (N.succ(` last))).
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
    NList.length pids_l + NList.length pids_r + 1 = Bsp.p.
    intros pids_l pids_r i H.
    rewrite <- pids_length, H.
    autorewrite with length.
    lia.
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
    clear H; destruct i; simpl in *; pid;
    try(rewrite N.pred_sub in H0; lia).
  Qed.
  
  Definition succ (i : pid) (H:i<>last) : pid :=
    exist (fun n=>n<?Bsp.p) (N.succ (` i)) (succ_aux H).

  Fact not_first_succ:
    forall i, i<>first -> exists j Hj, i = @succ j Hj.
  Proof.
    intros i H.
    assert(proj1_sig i <> 0) as H'
      by (contradict H; apply proj1_sig_inj; rewrite H; unfold first; auto).
    unfold succ; destruct i as [ i Hi ]; simpl in *.
    destruct i using N.peano_ind; try clear IHi.
    - contradiction.
    - assert(i<?Bsp.p) as Hi' by (clear H; pid).
      assert(of_N Hi' <> last) as Hlast.
      {
        unfold of_N; simpl; intro HH.
        assert(i = proj1_sig last) as HHH by now rewrite <- HH.
        unfold last in HHH; simpl in HHH.
        clear H; rewrite N.pred_sub in HHH; pid.
      }
      exists (of_N Hi'). exists Hlast.
      now apply proj1_sig_inj.
  Qed.
  
  Fact pred_aux :
    forall i : pid,  N.pred (`i) <? Bsp.p.
    intros [ i Hi ]; pid;
      try(now apply N.lt_lt_pred).
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
          clear i IH P H0 HS; pid;
        try(
            rewrite N.add_1_l in HSn;
            rewrite H in HSn;
            rewrite N.succ_pred in HSn by lia;
            lia).
      }
      assert(P i) by apply IH.
      match goal with
          [ |- P ?i' ] =>
          assert(i' = succ H) as H' by pid; rewrite H'
      end.
      now apply HS.
  Qed.
  
  Fact pid_up_to_aux (i:pid) :
    forall i',  In i' (NList.seq 0 (N.succ(` i))) ->
                i' <? Bsp.p.
    intros a H; apply In_seq in H; destruct i; pid.
  Qed.
  
  Definition pid_up_to (i:pid) : list pid :=
    Sig.map (P:=fun n=>n<?Bsp.p) (NList.seq 0 (N.succ (` i))) (pid_up_to_aux i).

  Lemma pid_up_to_firstn :
    forall j, pid_up_to j = NList.firstn (N.succ (` j)) pids.
  Proof.
    intros j; apply map_inj with (f:=@proj1_sig N (fun n=>n<?Bsp.p)).
    - apply proj1_sig_inj.
    - unfold pid_up_to; rewrite <- NList.firstn_map; unfold pids.
      repeat rewrite Sig.map_proj1_sig.
      rewrite firstn_seq.
      assert(N.min (N.succ (` j)) Bsp.p = N.succ (` j)) as Hmin
          by (apply N.min_l_iff; destruct j; pid).
      now rewrite Hmin.
  Qed.
  
  Definition from (i:pid) : list pid.
    refine(Sig.map (P:=fun n=>n<?Bsp.p) (NList.seq (` i) (Bsp.p-(`i))) _ ).
    intros n H; apply In_seq in H; pid.
  Defined.

  Definition from_succ (i:pid) : list pid.
    refine(if pid_dec i last
           then []
           else from (succ _)).
    exact n.
  Defined.
  
  Lemma from_le:
    forall i j, le i j ->
           In j (from i).
  Proof.
    intros i j H.
    rewrite (in_map_iff_inj _ _ proj1_sig_inj).
    unfold from; rewrite Sig.map_proj1_sig.
    apply In_seq. 
    autounfold with pid in *.
    split; auto; destruct i, j; simpl in *; pid.
  Qed.

  Lemma In_from_split:
    forall i j,
      In j (from i) ->
      exists H1 H2, from i = (Sig.map (NList.seq (` i) ( (` j) - (` i))) H1)
                          ++ j ::
                          (Sig.map (NList.seq (N.succ (` j)) ( Bsp.p - (N.succ (` j)) ) ) H2 ).
  Proof.
    intros i j Hin.
    repeat eexists.
    rewrite in_map_iff_inj in Hin by apply proj1_sig_inj.
    unfold from in Hin; rewrite Sig.map_proj1_sig in Hin.
    assert (N.le (` i) (` j)) by (apply In_seq in Hin ; pid).
    assert(forall x, In x [ ` j ] ->  x <? Bsp.p) as HIn_j.
    {
      clear.
      intros x H; simpl in H; destruct H as [ H | H ]; try now exfalso.
      destruct j; pid.
    }
    match goal with
      | [  |- _ = ?l1 ++ j :: ?l2  ] =>
        replace (j::l2) with ( (Sig.map [ ` j ] HIn_j) ++ l2 )
          by (simpl; f_equal; now apply proj1_sig_inj)
    end.
    rewrite List.app_assoc.
    erewrite Sig.map_pi with (l:=[` j])(l':=[` j]) by solve [ apply proj1_sig_inj | auto ].
    repeat rewrite <- Sig.map_app by apply proj1_sig_inj.
    unfold from; apply Sig.map_pi.
    - apply proj1_sig_inj.
    - rewrite <- List.app_assoc; simpl; apply In_seq_split in Hin; rewrite Hin.
      do 2 f_equal.
      now rewrite N.add_comm, N.sub_add by (destruct i; pid).
      Unshelve.
      intros a H.
      repeat (apply in_app_or in H; destruct H as [ H | H ]).
      + apply In_seq in H;  destruct H as [ H1 H2 ].
        destruct(N.le_decidable (` i) (` j)) as [ Hle | Hge ].
       * rewrite N.add_comm, N.sub_add in H2 by auto.
         destruct j as [ k Hk ]; simpl in *; clear H1; pid.
       * apply N.nle_gt in Hge.
         assert(` j <= ` i) as H by lia.
         rewrite <- N.sub_0_le in H; rewrite H, N.add_0_r in H2.
         destruct i; pid.
      + simpl in H; destruct H as  [ H | H ]; try now exfalso.
        rewrite <- H. destruct j; auto.
      + apply In_seq in H. destruct H as [ H1 H2 ].
        unfold succ in *; simpl in *.
        pid.
  Qed.

  Fact pids_from: pids = from first.
  Proof.
    unfold pids, from.
    apply Sig.map_pi.
    - apply proj1_sig_inj.
    - unfold first; simpl; now rewrite N.sub_0_r.
  Qed.

  
  Fact pid_up_to_last:
    pids = pid_up_to last.
    unfold pid_up_to; autounfold with pid.
    assert( forall a a' : pid, ` a = ` a' -> a = a') by pid.
    assert(NList.seq 0 Bsp.p =
           NList.seq 0 (N.succ(` last)) ) by (now rewrite S_last).
    now apply Sig.map_pi.
  Qed.
  
  Fact pids_snoc : pids = (removelast pids) ++ [ last ].
  Proof.
    rewrite app_removelast_last with (l:=pids)(d:=first) at 1
      by (rewrite pids_cons; intro H; discriminate).
    repeat f_equal.
    rewrite pid_up_to_last; unfold pid_up_to.
    erewrite Sig.map_pi with (l:=NList.seq 0 (N.succ(` last)))
                               (l':= (NList.seq 0 (` last)) ++ [` last ])
      by solve [ apply proj1_sig_inj | apply seq_S_app ].
    rewrite Sig.map_app by apply proj1_sig_inj; simpl.
    rewrite list_last_app.
    now apply proj1_sig_inj.
    Unshelve.
    intros a H; rewrite <- seq_S_app, In_seq in H; simpl in H.
    rewrite N.succ_pred in H by (pose Bsp.p_spec; lia).
    pid.
  Qed.

  Fact In_pid:
    forall (i:pid) x, In x [` i] -> x <? Bsp.p.
  Proof.
    simpl; intros i n Hin.
    destruct Hin as [ Heq | F ].
    - subst; pid.
    - now exfalso.
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
      rewrite Sig.map_pi with (l':=[ 0 ])(H':=In_pid first).
      + assert(Sig.map [0] (In_pid first) = [ first ]) as Heq
            by (simpl; f_equal; apply proj1_sig_inj; now simpl).
        now rewrite Heq.
      + apply proj1_sig_inj.
      + rewrite seq_S_app; simpl.
        now rewrite seq_equation.
    - auto.
  Qed.

  Lemma pid_up_to_succ :
    forall (i:pid) (Hi:i<>last),
      pid_up_to (succ Hi) = (pid_up_to i) ++ [succ Hi].
  Proof.
    intros i Hi; unfold pid_up_to.
    assert(forall i',In i' (NList.seq 0 (N.succ(` i)) ++
                                 [N.succ (` i)]) -> i' <? Bsp.p) as Hi'.
    {
      intros i' Hi'. apply in_app_or in Hi'. destruct Hi' as [Hi' | Hi'].
      - eapply pid_up_to_aux; eauto.
      - assert(i' = N.succ (` i)) by pid. subst.
        now apply succ_aux in Hi. 
    }
    assert(  Sig.map (NList.seq 0 (N.succ (` i))) (pid_up_to_aux i) ++ [succ Hi] =
            Sig.map (NList.seq 0 (N.succ (` i)) ++ [N.succ (` i)]) Hi' ) as Heq.
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
