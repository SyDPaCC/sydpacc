Require Import Coq.Lists.List Program NArith Omega. Import ListNotations.
Require Import SyDPaCC.Support.List SyDPaCC.Support.NList.
From SyDPaCC.Core Require Import Bmf Parallelization.
From SyDPaCC.Bsml.Model Require Import Core Pid.
Set Implicit Arguments.

(** * Distributed Arrays *)

Ltac destruct_da da :=
  let Hda := fresh "H" da in
  let content := fresh da "_content" in
  let indexes := fresh da "_indexes" in
  let length := fresh da "_length" in
  let distribution := fresh da "_distribution" in
  let coherence := fresh da "_coherence" in
  (destruct da as [da Hda];
   destruct da as [content indexes length distribution coherence];
   repeat let name := fresh da "_coherence" in 
          destruct coherence as [ name coherence ]).

Open Scope N_scope.

(** The module type [TYPE] provides an implementation of the Orleans
    Skeleton Library (OSL) programming model using Bulk Synchronous Parallel ML. *)

Module C(Import Bsml: BSML)(Import Pid : Pid.TYPE Bsml.Bsp).

  (** ** The data-structure *)

  Record da (A:Type) := make_da {
    da_content: par (list A);           
    da_first_index: par N; (* Binary natural numbers *)
    da_length: N;  (* Binary natural numbers *)
    da_distribution: list N; (* Binary natural numbers *)
    da_coherence: 
      length da_distribution = Bsp.p /\
      (forall pid, get da_first_index pid = 
              nth (proj1_sig pid) (scanl N.add 0 da_distribution) 0) /\ 
      da_length = List.fold_right Nplus 0 da_distribution /\
      forall pid, 
        length (get da_content pid) = 
        nth (proj1_sig pid) da_distribution 0
  }.

  Arguments da_length [A].
  Arguments da_distribution [A].
  Arguments da_content [A].
  Arguments da_first_index [A].

  Definition join A (v:da A) : list A :=
    List.flat_map (proj v.(da_content)) pids.

  Global Program Instance surjective_join (A:Type) : Surjective (join (A:=A)).
  Next Obligation.
    set(v := mkpar(fun pid =>if pid_dec first pid then y else [])).
    set(fi := mkpar(fun pid=>if N.eq_dec (` pid) 0 then 0 else (length y))).
    assert({ distributed_array: da A | join distributed_array = y}).
    {
      refine (exist _
                    (@make_da A v fi (length y) ((length y)::(List.map (fun _=>0) (seq 1 (Bsp.p-1)))) _)
                    _).
      { unfold join; simpl; apply pids_ind.
        - unfold v; simpl; autorewrite with bsml.
          case_eq(pid_dec first first);intros H _.
          + apply app_nil_r.
          + now contradict H.
        - intros i Hi IH. rewrite pid_up_to_succ.
          rewrite flatmap_app, IH. unfold v.
          simpl. autorewrite with bsml. 
          case_eq(pid_dec first (succ Hi));intros H _.
          + assert( N.succ (` i) = 0) as HH.
            {
              replace 0 with (` first) by auto.
              now rewrite H.
            }
            apply N.succ_0_discr in HH.
            now exfalso.
          + now repeat rewrite right_neutral. }
      Unshelve.
      repeat split.
      - autorewrite with length; pose (Bsp.p_spec); zify; omega.
      - intro pid; unfold fi; simpl; destruct pid as [ pid Hpid]; simpl in *.
        autorewrite with bsml; clear - Hpid.
        induction pid as [ | pid IH ].
        + trivial.
        + rewrite scanl_fold.
          * rewrite firstn_map, firstn_seq.
            simpl proj1_sig.
            destruct (N.eq_dec (N.pos pid) 1) as [ Heq | Heq ].
            -- rewrite Heq; simpl; rewrite N.min_0_l.
               now rewrite seq_equation.
            -- pid.
               assert(N.min (Pos.pred_N pid) (Bsp.p - 1) = Pos.pred_N pid) as Hmin.
               {
                 rewrite N.pos_pred_spec, N.pred_sub.
                 zify; omega.
               }
               rewrite Hmin.
               generalize dependent (Pos.pred_N pid); intros n Hn; clear.
               generalize dependent 1.
               induction n as [ | n IH ] using N.peano_ind; intro first.
               ++ now rewrite seq_equation.
               ++ rewrite seq_equation; destruct n; simpl.
                  ** rewrite N.add_0_r. now rewrite <- IH.
                  ** rewrite Pos.pred_N_succ, N.add_0_r. auto.
          * pose Bsp.p_spec; autorewrite with length.
            apply N.ltb_lt in Hpid.
            replace (1 + (Bsp.p -1) ) with Bsp.p by (zify; omega).
            set(n:=N.pos pid) in *; rewrite N.pred_sub; zify; omega.
      - pose Bsp.p_spec; autorewrite with length. pid.
        rewrite <- N.add_0_r at 1; f_equal.
        generalize dependent (Bsp.p-1); generalize dependent 1; clear.
        intros first size; generalize dependent first. 
        induction size as [ | n IH ] using N.peano_ind; intro first.
        + now rewrite seq_equation.
        + rewrite seq_equation; destruct n; simpl.
          * now rewrite <- IH.
          * now rewrite Pos.pred_N_succ.
      - intro pid; unfold v; autorewrite with bsml; simpl.
        destruct(pid_dec first pid) as [ Heq | Hdiff ].
        + rewrite <- Heq; unfold first; trivial.
        + destruct pid as [pid Hpid]; simpl.
          destruct pid as [ | pos ].
          * contradict Hdiff; apply proj1_sig_inj;
              simpl in *; auto.
          * rewrite nth_map with (default:=0)(fdefault:=0);
              clear Hdiff; pid.
            rewrite N.pos_pred_spec, N.pred_sub; zify; omega.
    }
    destruct X as [ x Hx].
    now exists x.
  Defined.

  Global Program Instance list_par_list_corr A :
    TypeCorr (@join A).

End C.

(** ** Module Type *)
Module Type T (Bsml: BSML)(Pid: Pid.TYPE Bsml.Bsp).
  Include C Bsml Pid.
End T.

Close Scope N_scope.

(*
  
  Lemma firstLocalIndexAtFirstProcessor:
    forall(A:Type)(d:da A),
      Bsml.get (da_first_index d) first = 0.
  Proof.
    intros A d.
    destruct d as [ content length first_index distribution coherence].
    destruct coherence as [ Hlen [ Hfirst H ]].
    simpl.
    rewrite Hfirst.
    unfold first. 
    simpl.
    destruct distribution; trivial.
  Qed.

  (*
  Definition evenlyDistributed {A:Type}(d : da A) : Prop := 
    forall (pid:processor), 
      NLength.length (BsmlPrimitives.get (da_content d) pid) =
      if N.ltb (N_of_nat (proj1_sig pid)) ( (da_length d) mod Nbsp_p )
        then ( ( da_length d)  / Nbsp_p ) + 1
        else (da_length d) / Nbsp_p.

  Definition distributedArray (A:Type) := { d : da A | evenlyDistributed d }.
   *)
  
  (** ** Basic operations on distributed arrays *)

  Program Definition length (A:Type)(d:da A) := da_length d.

  Arguments length [A].

  Definition get (A:Type)(d:distributedArray A)(i:N)(default:A) : A := 
    nth (nat_of_N i) (listOfParList (da_content (proj1_sig d))) default.

  Implicit Arguments get [A].
  
  Program Definition lengthOfContentIsLength: forall (A:Type)(d:distributedArray A), 
    NLength.length (listOfParList (da_content d)) = length d.
  Proof.
    intros A d. unfold length.
    destruct d as [d Hd]; destruct d as [content firstLocalIndex length distribution coherence].
    repeat (let tmp:=fresh "coherence" in 
          destruct coherence as [ tmp coherence]); simpl.
    rewrite coherence2.
    rewrite <- (@mapNthEq N distribution 0).
    replace (List.seq 0 (Datatypes.length distribution)) 
      with (listProj (proj1_sig processors))
        by (
          unfold processors; simpl; rewrite inSigProj;
            set(c0:=coherence0);rewrite Nlengthlength in c0;unfold Nbsp_p in c0;
              apply Nat2N.inj in c0; rewrite c0; trivial).
    unfold listProj; rewrite map_map, map_ext 
      with (g:=fun pid=> NLength.length (BsmlPrimitives.get content pid)); try (intro a; auto).
    unfold listOfParList.
    autorewrite with length.
    rewrite <- map_map with (g:=NLength.length (A:=A)). 
    rewrite map_ext with (g:=fun l => N.of_nat(List.length l)); try apply Nlengthlength.
    rewrite <- map_map with (g:=N.of_nat).
    apply NOfNatFoldAdd.
  Qed.
  
  Lemma getPropertyPosition: 
    forall (A:Type)(d:distributedArray A)(position:N)(default1 default2 : A), 
    position < length d -> get d position default1 = get d position default2.
  Proof.
    intros A d position default1 default2 H; unfold get, TYPE.length in *; 
      set(d':=d); 
      destruct d as [d Hd]; 
        destruct d as [content firstLocalIndex length distribution coherence]; simpl in *.
    apply nth_indep.
    rewrite lengthNlength.
    replace content with (da_content (proj1_sig d')) by auto. 
    rewrite lengthOfContentIsLength.
    replace (TYPE.length d') with length by auto.
    zify. omega.
  Qed.

  Program Definition getPropertyDefault: 
    forall (A:Type)(da:distributedArray A)(position:N)(default:A), 
    length da <= position -> get da position default = default.
  Proof.
    intros A da0 position default H; unfold get; simpl.
    rewrite nth_overflow; trivial.
     rewrite lengthNlength.
     rewrite lengthOfContentIsLength.
     zify. omega.
  Qed.

  Lemma listOfParListDistributedArray:
    forall (A:Type)(da: distributedArray A)(default : A),
      listOfParList (da_content (` da)) = 
      List.map (fun i : N => get da i default) (seq 0 (da_length (` da))).
  Proof.
    intros A da0 default; unfold get; simpl.
    rewrite seqNatSeq, map_map; simpl.
    set(H:=lengthOfContentIsLength); unfold length in H.
    rewrite <- H.
    rewrite Nlengthlength.
    rewrite nat_of_N_of_nat.
    rewrite map_ext 
            with (g:=fun x : nat => nth x
                                        (listOfParList (da_content (` da0)))
                                        default).
    rewrite mapNthEq; trivial.
    intro a; rewrite nat_of_N_of_nat; trivial.
  Qed.

  Lemma daLengthSubDa:
    forall (A:Type)(d: distributedArray A)(pid:processor),
      let getLength := fun pid => List.length(BsmlPrimitives.get (da_content (` d)) pid) in
      (fold_right plus 0 (map getLength (processorsUpTo pid)) <= N.to_nat (length d))%nat.
  Proof.
    intros A d pid getLength.
    destructDa d. unfold length. Opaque processorsUpTo. simpl. 
    rewrite d_coherence2.
    unfold evenlyDistributed, length in *; simpl in *.
    rewrite <- mapNthEq with (l:=d_distribution)(default:=0).
    rewrite Nlengthlength in d_coherence0. unfold Nbsp_p in d_coherence0.
    apply Nat2N.inj in d_coherence0.
    rewrite d_coherence0.
    rewrite <- inSigMapProj1Sig with (P:=fun n=>(n < bsp_p)%nat)
            (l:=List.seq 0 bsp_p)(H:=inSeq0Lt bsp_p).
    rewrite map_map.
    rewrite map_assumption 
            with (g:=fun pid=>N.of_nat (List.length((BsmlPrimitives.get d_content pid))))
            by (intros x H; rewrite <- d_coherence; apply Nlengthlength).
    replace 0%N with (N.of_nat 0%nat) by auto.
    rewrite <-map_map with (g:=N.of_nat), <- NOfNatFoldAdd.
    rewrite Nat2N.id.
    replace (inSig (fun n : nat => (n < bsp_p)%nat) (List.seq 0 bsp_p) (inSeq0Lt bsp_p))
            with (` processors) by auto.
    destruct (splitProcessorsUpTo pid) as [remainingProcessors Hrp].
    rewrite Hrp, map_app, fold_right_app.
    assert(forall (l:list nat)(a:nat), (a <= fold_right plus a l)%nat) as HfoldA
          by (induction l; trivial; simpl; intro b; specialize (IHl b); omega).
    assert(forall (l:list nat)(a:nat), 
             (fold_right plus 0 l <= fold_right plus a l)%nat) as HfoldL
          by (induction l; intros b; simpl; [|specialize (IHl b)]; omega).
    unfold getLength.
    apply HfoldL.
  Qed.

  (** * Compatibility of distributed arrays for the [zip] skeleton *)
  Class compatible {A B:Type}(da1: distributedArray A)(da2: distributedArray B) := {
    compatibleProperty: length da1 = length da2
  }.

  Lemma compatibleCommutative {A B : Type} (da1: distributedArray A)
                              (da2: distributedArray B){comp: compatible da1 da2} 
    : compatible da2 da1.
  Proof.
    apply Build_compatible.
    symmetry.
    apply compatibleProperty.
  Qed.
  
  Class sameDistribution {A B:Type}(da1: distributedArray A)(da2: distributedArray B) := {
    sameDistributionProperty : 
    da_distribution (proj1_sig da1) = da_distribution (proj1_sig da2) 
  }.

  Instance evenlyDistributedCompatibleSameDistribution 
    {A B:Type}(da1: distributedArray A)(da2: distributedArray B)
    {comp: compatible da1 da2} : sameDistribution da1 da2.
  Proof.
    constructor; destruct da1 as [da1 Hda1], da2 as [da2 Hda2]; 
      destruct da1, da2; unfold evenlyDistributed in *; set(H:= compatibleProperty);
        simpl in *.    
    repeat 
      let newH := fresh "H" in
        destruct da_coherence0 as [newH da_coherence0];
    repeat 
      let newH := fresh "H" in
        destruct da_coherence1 as [newH da_coherence1].
    apply Nth.nthSameLengthEqual with (d:=0).
    repeat rewrite lengthNlength; rewrite H1, H0; trivial.
    intros n Hn.
    assert(List.length da_distribution0 = bsp_p) as Hbsp.
    apply Nat2N.inj.
    rewrite <- Nlengthlength.
    assumption.
    rewrite Hbsp in Hn.
    set(procN:=buildBoundedNat Hn).
    replace n with (proj1_sig procN) by auto.
    rewrite <- da_coherence1, <- da_coherence0.
    rewrite Hda1, Hda2.
    unfold length in H; simpl in H.
    rewrite H; trivial.
  Qed.

  Lemma compatibleSameLengthOnPid:
    forall (A B : Type)(da1: distributedArray A)(da2: distributedArray B)
           {sl: compatible da1 da2}(pid:processor),
      NLength.length(BsmlPrimitives.get (da_content (` da1)) pid) =
      NLength.length(BsmlPrimitives.get (da_content (` da2)) pid).
  Proof.
    intros A B da1 da2 sl pid.
    unfold evenlyDistributed in *.
    destruct da1, da2.
    rewrite e, e0. 
    set(H:=compatibleProperty); unfold length in *; simpl in H.
    rewrite H; trivial.
  Qed.

  Instance compatibleSame (A :Type)(da:distributedArray A): 
    compatible da da.
  Proof.
    constructor; auto.
  Qed.


*)