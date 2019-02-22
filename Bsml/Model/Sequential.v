Require Import Coq.Lists.List Program NArith Omega.
From SyDPaCC.Bsml.Model Require Import Core Pid.
From SyDPaCC.Support Require Import UIP Sig List NList.

(** * A Certified Sequential Implementation of BSML *)

(** In order to check that the axiomatization of the BSML library
    makes sense, we implement the [BSML] module type using lists. *)

Open Scope N_scope.

Module Implementation (Import B : BSP_PARAMETERS) <: BSML.

  Module Bsp := B.

  Notation pid := { n : N | N.ltb n Bsp.p = true }.

  Module Import Pid := Pid.Make Bsp.

  (** ** Parallel Vectors: Implemented as Lists of Size [Bsp.p] *)
  Definition par (A:Type) := { l : list A | length l = Bsp.p }.

  Program Definition get {A:Type}(v:par A)(i:pid) : A := `(Sig.nth (`v) i).
  Next Obligation.
    destruct v as [v Hv]; simpl; rewrite Hv.
    now apply N.ltb_lt.
  Qed.

  Lemma bsp_pSMaxPid: 
    exists maxPid:N, Bsp.p = N.succ maxPid.
  Proof.
    destruct Bsp.p as [| maxpid Hmaxpid] eqn:Hp using N.peano_ind.
    - set(H:=Bsp.p_spec). contradict Hp; zify; omega.
    - exists maxpid; trivial.
  Qed.

  Program Definition pid0 : pid := 0.
  Next Obligation. pid. Qed.

  Lemma par_eq : 
    forall (A:Type)(v v':par A),
    (forall (i:pid), get v i = get v' i) -> v = v'.
  Proof.
    intros A [v Hv] [v' Hv'] H. unfold get in *. simpl in H.
    assert(length v = length v') as Hlen by (clear H; now rewrite <- Hv in Hv'); subst.
    assert(v = v').
    {
      apply Sig.nth_eq with (H:=Hlen). intros pos.
      assert((`pos)<Bsp.p) as Hi by
            (destruct pos as [pos Hpos ]; pid; now rewrite Hv in Hpos).
      specialize (H (of_N' Hi)).
      match goal with 
        | [ H : Sig.nth ?l1 ?pos1 = Sig.nth ?l2 ?pos2 |- _] =>
          transitivity (Sig.nth l1 pos1)
      end.
      eapply Sig.nth_pi; eauto.                  
      match goal with 
        | [ H : Sig.nth ?l1 ?pos1 = Sig.nth ?l2 ?pos2 |- _] =>
          transitivity (Sig.nth l2 pos2); auto
      end.
      eapply Sig.nth_pi; eauto; destruct pos; pid.
    }
    subst. now replace Hv with Hv' by (apply UIP).
  Qed.

  (** ** BSML Primitives *)
  Program Definition 
    mkpar {A:Type}(f: pid -> A) : par A :=
    map f pids.
  Next Obligation.
    pid.
  Qed.
  
  Lemma mkpar_spec:
    forall (A:Type)(f:pid->A)(i:pid),
      get (mkpar f) i = f i.
  Proof.
    intros A f i.
    unfold get, mkpar, pids; simpl.
    rewrite Sig.nth_map, Sig.map_nth by (intros; apply Bool.UIP).
    f_equal; apply proj1_sig_inj; simpl.
    rewrite Sig.nth_spec with (default:=0); simpl.
    rewrite seq_seq.
    replace 0 with (N.of_nat 0%nat) by auto.
    rewrite map_nth, seq_nth;
      destruct i; pid.
  Qed.
    
  Program Definition apply {A B:Type}(vf:par(A->B))(vx: par A):
    par B := 
    map(fun (p:((A->B)*A)) => let (f,v):=p in f v)
       (combine vf vx).
  Next Obligation.
    destruct vf as [vf H], vx as [vx H']; simpl.
    length; 
    now rewrite H, H'.
  Qed.
  
  Lemma apply_spec:
    forall (A B:Type)(vf:par(A->B))(vx: par A)
           (i:pid),
      get(apply vf vx) i = (get vf i)(get vx i).
  Proof.
    intros A B [vf Hvf] [vx Hvx] i.
    unfold get, apply; simpl.
    assert(length vf = length vx) as Hlen by now rewrite Hvf, Hvx.
    rewrite Sig.nth_map, (Sig.nth_combine _ _ _ Hlen).
    pose(pos_f:=Sig.cast_sig (of_pid i) (Sig.lt_eq (eq_sym Hvf))).
    pose(pos_x:=Sig.cast_sig (of_pid i) (Sig.lt_eq (eq_sym Hvx))).
    rewrite Sig.nth_pi with (pos2:=pos_f) by auto.
    rewrite Sig.nth_pi with (l:=vx)(pos2:=pos_x) by auto.
    symmetry.
    rewrite Sig.nth_pi with (pos2:=pos_f) by auto.
    rewrite Sig.nth_pi with (l:=vx)(pos2:=pos_x) by auto.
    trivial.
  Qed.
  
  Program Definition put {A:Type}(vf: par (pid -> A)):
    par(pid -> A) :=
    map
      (fun (dst src:pid)=>(Sig.nth vf src) dst)
      pids.
  Next Obligation.
    destruct vf as [vf Hvf]; simpl.
    pid; intuition.
  Qed.
  Next Obligation. length. Qed.
  
  Lemma put_spec:
    forall(A:Type)(vf: par (pid -> A))
          (i j : pid),
      get (put vf) i j = get vf j i.
  Proof.
    intros A [vf Hvf] i j. 
    unfold get, put; simpl.
    rewrite Sig.nth_map.
    set(pos:=Sig.cast_sig (of_pid j) (Sig.lt_eq (eq_sym Hvf))).
    set(pos':=Sig.cast_sig (of_pid i) (Sig.lt_eq (eq_sym pids_length))).
    rewrite Sig.nth_pi with (pos2:=pos) by auto.
    rewrite Sig.nth_pi with (l:=pids)(pos2:=pos') by auto.
    symmetry.
    rewrite Sig.nth_pi with (pos2:=pos) by auto.
    f_equal; symmetry.
    unfold pids; rewrite Sig.map_nth by (intros; apply Bool.UIP); simpl.
    apply proj1_sig_inj; simpl.
    rewrite Sig.nth_spec with (default:=p); simpl.
    rewrite seq_seq.
    destruct i, j; simpl; clear pos pos'. rewrite <- (N2Nat.id  p).
    rewrite map_nth, seq_nth; pid.
  Qed.
  
  Definition proj {A:Type}(v: par A) : pid -> A :=
    get v.

  Lemma proj_spec:
    forall(A:Type)(v:par A)(i:pid),
      (proj v) i = get v i.
    auto.
  Qed.
  
End Implementation.

Close Scope N_scope.

