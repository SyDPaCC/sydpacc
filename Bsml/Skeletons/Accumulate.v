Require Import Coq.Lists.List Program NArith Lia. Import ListNotations.
Require Import SyDPaCC.Support.List SyDPaCC.Support.NList.
From SyDPaCC.Core Require Import Bmf Parallelization Diffusion.
From SyDPaCC.Bsml.Model Require Import Core Pid.
From SyDPaCC.Bsml.DataStructures Require Import DistributedList DistributedVector.
From SyDPaCC.Bsml.Skeletons Require Import StdLib.
Set Implicit Arguments.
Generalizable All Variables.

Module Make(Import Bsml: BSML)
       (Import Pid: Pid.TYPE Bsml.Bsp)
       (Import StdLib: StdLib.TYPE Bsml Pid)
       (Import PL : DistributedList.T Bsml Pid)
       (Import DV : DistributedVector.T Bsml Pid).

  Open Scope N_scope.
  Open Scope sydpacc_scope.

  
  (** * The [last] Skeleton *) 
 
  Definition seq_last A (l : list A | length l = Bsp.p) : A.
    pose Bsp.p_spec.
    refine (Bmf.last (` l)).
    now apply length_lt_0_NonEmpty.
  Defined.
  
  Definition par_last A (v:par A) : A := proj v Pid.last.

  #[export] Instance last_corr A: FunCorr (@seq_last A) (@par_last A).
  Proof.
    repeat constructor; intros ap; unfold join, seq_last, last; simpl.
    unfold Bmf.last; rewrite pids_snoc at 1.
    rewrite map_app; simpl; now rewrite list_last_app.
  Qed.


  (** * The [put_right_list] Communication Function *) 

  Definition put_right_list A (v:par A) : par(list A) :=
    let destinations := mkpar(fun pid=>Pid.from_succ pid) in
    let messages := 
        parfun2 (fun last=>List.map (fun dst=>(dst,last))) v destinations in
    put_list messages.

  Fact put_right:
    forall A (v:par A) i j (Hlast: j<>Pid.last),
      Pid.le i j ->
      get
        (put
           (parfun (fun (listDstValue : list (pid * A)) (dst : pid) => assoc dst listDstValue)
                   (parfun2 (fun last0 : A => map (fun dst : pid => (dst, last0))) v
                            (mkpar (fun pid : pid => from_succ pid))))) (succ Hlast) i = Some(get v i).
  Proof.
    intros A v i j Hlast Hi.
    autorewrite with bsml.
    apply assoc_in_first. unfold from_succ.
    destruct(pid_dec i Pid.last) as [ Heq | Hneq ].
    - assert(j = Pid.last).
      {
        subst; destruct j as [ j Hj ]; unfold last, le in *; simpl in *; pid.
        apply proj1_sig_inj; simpl; clear Hlast H;
          rewrite N.pred_sub in Hi; pid;
        try(apply N.le_lteq in Hi;
            destruct Hi as [Hi|Hi];
            [ lia | rewrite N.pred_sub; auto ]).
      }
      contradiction.
    - assert(le (succ Hneq) (succ Hlast)) as Hle.
      {
        unfold le, succ in *; simpl in *.
        lia.
      }
      apply from_le in Hle; auto.
      apply In_from_split in Hle.
      destruct Hle as [ H1 [ H2 Hfrom ] ].
      rewrite Hfrom; repeat rewrite map_app; simpl.
      match goal with
      | [ |- in_first ?pair (?l1'++_::?l2') ] => 
        apply in_first_ with (l1:=l1')(l2:=l2')(l:=l1'++pair::l2')
      end.
      + simpl; intros b H.
        apply in_map_iff in H; destruct H as [ k [Hk1 Hk2]].
        inversion Hk1; subst; clear Hk1.
        apply Sig.in_map_in in Hk2; unfold succ in Hk2; simpl in Hk2.
        apply In_seq in Hk2; destruct Hk2 as [ Hk1 Hk2 ].
        pid.
      + reflexivity.
  Qed.

  Lemma put_right_list_first:
    forall A (v:par A),
      get (put_right_list v) first = [ ].
  Proof.
    intros A v.
    unfold put_right_list, put_list; autorewrite with bsml.
    apply filter_map_some_empty.
    intros j Hj. autorewrite with bsml.
    apply assoc_not_in.
    rewrite map_map; simpl; rewrite map_id.
    intro H.
    apply in_map with (f:=@proj1_sig N _) in H; simpl in H.
    unfold from_succ in H.
    destruct(pid_dec j Pid.last) as [ Heq | Hneq ].
    - inversion H.
    - unfold from in H; rewrite Sig.map_proj1_sig in H.
      apply In_seq in H.
      unfold succ in H; simpl in H; lia.
  Qed.
    
  Lemma put_right_list_succ:
    forall A (v:par A) j (Hlast: j<>Pid.last),
      get (put_right_list v) (succ Hlast) =
      map (get v) (pid_up_to j).
  Proof.
    intros A v j Hlast; unfold put_right_list, put_list; autorewrite with bsml.
    apply map_inj with (f:=Some).
    - intros a a' H0; now inversion H0.
    - rewrite filter_map_some_prop.
      assert(In j (from first)) as Hin
          by (rewrite <- pids_from; apply pids_spec).
      destruct (In_from_split first j Hin) as [ H1 [H2 Hfrom ]].
      rewrite pids_from; unfold from in *.
      erewrite Sig.map_pi
      with (l:=(seq (` first) (Bsp.p - ` first)))
             (l':=(seq (` first) (Bsp.p - ` first))) by solve [ apply proj1_sig_inj | auto ].
      rewrite Hfrom; clear Hfrom Hin.
      repeat rewrite map_app; simpl.
      rewrite put_right by (unfold le; pid).
      match goal with
      | [ |- filter _ ( (map ?f' _) ++ _ :: (map ?f'' _) )  = _ ] => 
        rewrite map_ext_in with (f:=f')(g:=fun i=>Some(get v i));
          try rewrite map_ext_in with (f:=f')(g:=fun i=>None)
      end.
      rewrite filter_app; simpl.
      rewrite filter_true, filter_false, map_map.
      + unfold pid_up_to.
        match goal with
        | [ |- map ?f ?l1 ++ [ Some(get _ ?k) ] = map ?f' ?l2 ] =>
          replace [ Some(get _ k) ] with (map f [ k ]) by auto;
            rewrite <- map_app;
            assert(l1 ++ [ k ] = l2) as Hl
        end.
        {
          replace [ j ] with (Sig.map [` j] (In_pid j))
            by (simpl; f_equal; now apply proj1_sig_inj).
          match goal with
          | [ |- Sig.map ?ll _ ++ _ = _ ] => 
            erewrite Sig.map_pi with (l:=ll)(l':=ll)
              by solve [apply proj1_sig_inj | auto ]
          end.
          erewrite Sig.map_pi with (l:=[` j])(l':=[` j])
            by solve [apply proj1_sig_inj | auto ].
          rewrite <- Sig.map_app by apply proj1_sig_inj.
          match goal with
          | [ |- Sig.map ?l1 _ = Sig.map ?l2 _ ] =>
            assert(l1 = l2) as Hl'
                by (rewrite seq_S_app; repeat f_equal; pid)
          end.
          erewrite Sig.map_pi with (l':=seq 0 (N.succ (` j)))
            by solve [apply proj1_sig_inj | auto ].
          reflexivity.
        }
        rewrite Hl.
        apply map_ext.
        intro; now autorewrite with bsml.
      + intros a Ha; apply in_map_iff in Ha; destruct Ha as [ x [ Hx1 Hx2 ] ]; now subst.
      + intros a Ha; apply in_map_iff in Ha; destruct Ha as [ x [ Hx1 Hx2 ] ]; now subst.
      + intros a Ha; autorewrite with bsml.
        apply assoc_not_in; rewrite map_map, map_id; simpl.
        apply Sig.in_map_in, In_seq in Ha; destruct Ha as [ Ha _ ].
        unfold from_succ; destruct(pid_dec a Pid.last) as [ Heq | Hneq ]; intro Hin.
        * inversion Hin.
        * unfold from in Hin.
           apply Sig.in_map_in, In_seq in Hin; destruct Hin as [ Hin _ ].
           unfold succ in Hin; simpl in Hin; pid.
      + intros a Ha; rewrite put_right; auto.
        apply Sig.in_map_in, In_seq in Ha; destruct Ha as [ _ Ha  ].
        rewrite N.sub_0_r, N.add_0_l in Ha.
        unfold le; pid.
        Unshelve.
        clear; intros a.
        replace [` j] with [0 + ` j] by auto.
        rewrite N.sub_0_r , <- seq_S_app.
        intro Ha; apply In_seq in Ha; destruct j; pid.
  Qed.
  
  (** * The [scanl1] Skeleton *) 
   
  Definition par_scanl1 A B op (e:B) (v:par A) : par B :=
    parfun (fun l=>List.fold_left op l e) (put_right_list v).    

  Definition seq_scanl1 A B (op:B->A->B) (e:B) (l:list A | length l = Bsp.p) :
    { l : list B | length l = Bsp.p }.
    exists(removelast(scanl op e (` l))).
    autorewrite with length; try typeclasses eauto.
    rewrite N.add_1_l, N.pred_succ.
    destruct l ; auto.
  Defined.

  Global Instance scanl1_scanl A B (op:B->A->B) e : FunCorr (seq_scanl1 op e) (par_scanl1 op e).
  Proof.
    constructor; intros ap Ha.
    unfold join, seq_scanl1, par_scanl1; apply list_length_inj; simpl.
    apply  pids_ind ; [ | intros j Hlast IH ].
    - simpl; f_equal; autorewrite with bsml.
      now rewrite put_right_list_first.
    - rewrite pid_up_to_succ.
      repeat rewrite map_app.
      rewrite IH; simpl. rewrite scanl_snoc, removelast_app by (intro;discriminate).
      autorewrite with bsml.
      rewrite put_right_list_succ; simpl; rewrite app_nil_r; symmetry.
      rewrite scanl_scanl_last, scanl_last_fst_scanl at 1.
      do 2 f_equal.
      rewrite scanl_last_snd.
      f_equal; apply map_ext.
      intro; now autorewrite with bsml.
  Qed.
  
  Lemma scanl1_spec:
    forall A B op (e:B) (v:par A) pid,
      get (par_scanl1 op e v) pid = nth (` pid) (scanl op e (` (join v))) e.
  Proof.
    intros A B op e v pid; unfold par_scanl1.
    autorewrite with bsml.
    destruct(pid_dec pid first) as [ Heq | Hneq ]; subst.
    - rewrite put_right_list_first; simpl.
      now rewrite scanl_cons, nth_equation.
    - apply not_first_succ in Hneq.
      destruct Hneq as [ j [ Hj Heq ] ]; subst.
      rewrite put_right_list_succ.
      rewrite scanl_fold by
          (unfold succ; unfold join; rewrite N.add_1_l; simpl;
           autorewrite with length; repeat rewrite N.add_1_l; simpl;
           destruct j as [j Hj']; clear Hj; pid).
      unfold join; simpl.
      rewrite firstn_map; f_equal; rewrite pid_up_to_firstn by auto.
      apply map_ext; intro; now autorewrite with bsml.
  Qed.

  Lemma scanl1_seq_scanl1: forall A B op (e:A) (ap:par B),
      proj1_sig(join (par_scanl1 op e ap)) = proj1_sig (seq_scanl1 op e (join ap)).
  Proof.
    intros A B op e ap.
    pose (last_corr A) as H; inversion H as [ Hcorr ].  
    pose (scanl1_scanl op e) as H'; inversion H' as [ Hcorr' ].
    now rewrite Hcorr'.
  Qed.
  
  (** * The [scan_last] Skeleton *) 
  
  Definition par_scanl_last A B op1 op2 (e:B) c (v:par(list A)) : par(list B) * B :=
    let partials := parfun (scanl_last' op1 e) v in
    let scanls   := parfun fst partials in 
    let lasts    := parfun snd partials in
    let sums     := par_scanl1 op2 c lasts in
    ( parfun2 (fun sum=>map' (op2 sum)) sums scanls,
      par_last (parfun2 op2 sums lasts) ).

  Lemma parfun_seq_scanl_last_up_to:
    forall A B op e `{Monoid A op e} (q:B->A) c ap i,
      let op' := fun s t=>op s (q t) in
      fold_left op (map (proj (parfun snd (parfun (scanl_last op' e) ap))) (pid_up_to i)) c =
      fold_left op (map q (flat_map (proj ap) (pid_up_to i))) c.
  Proof.
    intros A B op e H q c ap i; induction i as [ | i Hneq IH ] using pid_ind.
    - replace (pid_up_to first) with [ first ]
        by (eapply map_inj;
            [ apply proj1_sig_inj |
              unfold pid_up_to; repeat rewrite Sig.map_proj1_sig;
              simpl; now repeat (rewrite seq_equation; simpl) ]).
      simpl.
      rewrite app_nil_r; autorewrite with bsml.
      rewrite scanl_last_snd.
      rewrite fold_left_map_r.
      rewrite <- fold_left_prop by typeclasses eauto.
      now rewrite right_neutral.
    - simpl; rewrite pid_up_to_succ, map_app, flatmap_app, map_app.
      repeat rewrite fold_left_app; simpl; rewrite app_nil_r.
      rewrite IH; autorewrite with bsml.
      rewrite scanl_last_snd.
      repeat rewrite fold_left_map_r with (g:=q).
      rewrite  <- fold_left_prop by typeclasses eauto; f_equal.
      apply right_neutral.
  Qed.
  
  Fact parfun_seq_scanl_last_pids:
    forall A B op (e:A) `{Monoid A op e} (q:B->A) c ap,
      let op' := fun s t=>op s (q t) in
      fold_left op (map (proj (parfun snd (parfun (scanl_last op' e) ap))) pids) c =
      fold_left op (map q (flat_map (proj ap) pids)) c.
  Proof.
    intros; rewrite pid_up_to_last.
    now apply parfun_seq_scanl_last_up_to.
  Qed.
     
  #[export] Instance scanl_last_corr A B `{Monoid A op e} (q:B->A) c:
    FunCorr (scanl_last (fun s t=>op s (q t)) c) (par_scanl_last (fun s t=>op s (q t)) op e c).
  Proof.
    repeat constructor; intros ap Ha;  unfold pairing; simpl.
    repeat rewrite parfun_ext with (g:=@scanl_last A B  (fun (s : A) (t : B) => op s (q t)) e)
      by (intro; now rewrite scanl_last_scanl_last').
    rewrite surjective_pairing, scanl_last_fst_scanl, <- last_scanl; f_equal.
    - unfold PL.join. apply pids_ind.
      + simpl; autorewrite with bsml; repeat rewrite app_nil_r.
        rewrite scanl_last_fst_scanl.
        set( op' := fun s t=>op s (q t)).
        specialize (scanl1_seq_scanl1 op c (parfun snd (parfun (scanl_last op' e) ap))) as Heq.
        unfold join, seq_scanl1, last in Heq; simpl in Heq; rewrite pids_cons in Heq;
          simpl in Heq; rewrite scanl_cons in Heq.
        assert(get (par_scanl1 op c (parfun snd (parfun (scanl_last op' e ) ap))) first = c) as HH
          by ( inversion Heq as [ H1 ]; rewrite H1; now autorewrite with bsml in H1 ).
        rewrite map'_map. rewrite HH, <- removelast_map; f_equal.
        unfold op'; now rewrite scanl_map_gen with (c:=c)(e:=e) by typeclasses eauto.
      + intros i Hlast_i IH.
        rewrite pid_up_to_succ, flatmap_app, flatmap_app; simpl;
          repeat rewrite app_nil_r; autorewrite with bsml; rewrite IH; clear IH.
        rewrite scanl1_spec, scanl_fold by
            (unfold succ, join; repeat rewrite N.add_1_l; simpl;
             autorewrite with length; repeat rewrite N.add_1_l;
             clear; destruct i; pid).
        simpl. rewrite firstn_map, <- pid_up_to_firstn by auto.
        rewrite parfun_seq_scanl_last_up_to by auto.
        rewrite <- fold_left_map_r with (g:=q).
        rewrite scanl_last_fst_scanl, <- scanl_last_snd, <- last_scanl.
        rewrite  map'_map,<- removelast_map, <- removelast_app by apply non_emptiness; f_equal.
        unfold Bmf.last; rewrite scanl_hd.
        erewrite scanl_app_gen by typeclasses eauto; f_equal.
        now rewrite list_last_non_empty with (d':=e) by typeclasses eauto.
    - autounfold in *. pose (last_corr A) as Hlc; inversion Hlc as [ Hcorr ].
      autounfold in *. rewrite Hcorr by auto; unfold seq_last, Bmf.last; simpl.
      rewrite pids_snoc, map_app at 1; simpl; rewrite list_last_app.
      autorewrite with bsml in *.
      rewrite scanl1_spec, scanl_fold, scanl_last_snd
        by (unfold succ, join; rewrite N.add_1_l; simpl;
            autorewrite with length; repeat rewrite N.add_1_l; simpl;
            rewrite N.pred_sub; clear; pid).
      pose  last_scanl as HH; unfold Bmf.last in HH; repeat rewrite HH.
      rewrite scanl_last_snd.
      unfold PL.join, join; simpl.
      repeat rewrite fold_left_map_r with (g:=q).
      erewrite <- parfun_seq_scanl_last_pids by typeclasses eauto.
      rewrite pids_snoc at 2; rewrite map_app, fold_left_app; simpl.
      rewrite firstn_map; repeat f_equal.
      + rewrite pids_snoc at 1.
        replace(N.pred Bsp.p) with (length(removelast pids))
          by (autorewrite with length; auto; rewrite pids_cons; typeclasses eauto).
        now rewrite firstn_app1, firstn_length by lia.
      + autorewrite with bsml.
        rewrite scanl_last_snd.
        now rewrite fold_left_map_r with (g:=q).
  Qed.

  Ltac sd :=
    match goal with
    | [ |- context [ SameDistribution ] ] =>
      intros; constructor; autounfold; intros; simpl;
      repeat (try rewrite <- scanl_last_scanl_last';try rewrite map'_map;
              autorewrite with bsml length)
    end.
  
  #[export] Instance preserves_distribution_fst_par_scanl_last A B op1 op2 (e:B) c:
    EnsuresProp (((id×fst)△(snd∘snd))∘(id △ (par_scanl_last op1 op2 e c)))
                ((prod_curry (@SameDistribution A B)) ∘ fst).
  Proof.
    constructor; intro v; now sd.
  Defined.

  (** * The [fold_left2] Skeleton *)

  Definition par_fold_left2 A B C (op1:C->A*B->C) (op2:C->C->C) (e:C)
             (v1:par(list A)) (v2:par(list B)) : C :=
    let f := proj (parfun2 (fold_left2 op1 e) v1 v2) in
    List.fold_left op2 (map f pids) e.

  
  #[export] Instance fold_left2_corr A B C (p:A*B->C) `{Monoid C op e} :
    let op' := fun (u:C) (vw:A*B)=>op u (p vw) in
    FunCorr2 (Bmf.fold_left2 op' e) (par_fold_left2 op' op e).
  Proof.
    constructor; intros ap bp H'; unfold par_fold_left2, PL.join; apply pids_ind;
    inversion H' as [ Hsd ]; subst; clear H'.
    - simpl; repeat rewrite app_nil_r; autorewrite with bsml.
      now rewrite left_neutral.
    - intros i Hi IH; rewrite pid_up_to_succ, <- fold_left2_prop1.
      repeat rewrite map_app; repeat rewrite flatmap_app; 
        rewrite combine_app
        by(length; repeat rewrite map_map; f_equal; apply map_ext;
           intro; autorewrite with bsml; auto).
      simpl; repeat rewrite app_nil_r; repeat rewrite fold_left_app; simpl;
        autorewrite with bsml; autounfold in *; rewrite IH; repeat rewrite <- fold_left2_prop1.
      repeat rewrite fold_left_map_r with (g:=p).
      rewrite <- fold_left_prop by typeclasses eauto; f_equal.
      apply right_neutral.
  Qed.
      
  (** * The [accumulate] Skeleton *)

  Open Scope sydpacc_scope.
  
  #[export] Instance parallelize_accumulate A B C (g:B->C) (p:A*B->C) (q:A->B)
           `{Monoid C oplus e_oplus} `{Monoid B otimes e_otimes} c :
    FunCorr
      (accumulate g p q oplus otimes c)
      ((prod_curry oplus)
         ∘ ( ((prod_curry (par_fold_left2 (fun (u:C) (vw:A*B)=>oplus u (p vw)) oplus e_oplus)) × g)
               ∘ ( ( (id × fst) △ (snd ∘ snd) )
                     ∘ (id △ (par_scanl_last (fun s t=>otimes s (q t)) otimes e_otimes c) ) ) ) )
      (HP:=true_parprop).
  Proof.
    typeclasses eauto.
  Qed.

  Close Scope sydpacc_scope.

  Close Scope N_scope.
  
End Make.
