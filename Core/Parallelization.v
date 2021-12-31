Require Import SyDPaCC.Core.Bmf.
Require Import Coq.Lists.List. Import ListNotations.
Generalizable All Variables.
Set Implicit Arguments.

Open Scope sydpacc_scope.

(** * Classes for Automatic Parallelization *)

Class Surjective A B (f:A->B) :=
  { surjective :  forall y : B,  exists x : A,  f x = y  }.

(** ** Type Correspondence *)

Class TypeCorr (seq_t:Type) (par_t:Type) (join:par_t->seq_t) :=
  { type_corr :> Surjective join }.

(** *** Instances: Composition of Type Correspondence *)

#[export] Instance tc_nopar (A:Type) : TypeCorr (fun x:A=>x) | 2000.
Proof.
  repeat constructor; intro; eexists; reflexivity.
Qed.

#[export] Instance tc_corr_pairs
         `{TypeCorr seqA parA joinA}
         `{TypeCorr seqB parB joinB} :
  @TypeCorr (seqA * seqB)%type (parA * parB) (joinA × joinB).
Proof.
  repeat constructor; intros pair.
  unfold pairing.
  assert(exists x, joinA x = fst pair) as [ xA HA] by apply surjective.
  assert(exists x, joinB x = snd pair) as [ xB HB] by apply surjective.
  exists (xA,xB); now rewrite surjective_pairing; f_equal.
Qed.

(** ** Function Correspondence *)

Class ParProp `{HA:TypeCorr A Ap} (P:Ap->Prop) :=
  { par_prop := P }.

#[export] Instance true_parprop  `{HA:TypeCorr A Ap} :
  ParProp (fun x:Ap=>True) | 2000 := {}.

Class Par2Prop `{HA:TypeCorr A Ap} `{HB:TypeCorr B Bp} (P:Ap->Bp->Prop) :=
  { par2_prop := P }.

#[export] Instance true_par2prop  `{HA:TypeCorr A Ap} `{HB:TypeCorr B Bp} :
  Par2Prop (fun (_:Ap) (_:Bp)=>True) | 2000 := {}.

#[export] Instance true_par2prop_and  `{HA:TypeCorr A Ap} `{HB:TypeCorr B Bp} :
  Par2Prop (fun (_:Ap) (_:Bp)=>True /\ True) | 2000 := {}.

Class FunCorr
      `{ACorr : TypeCorr A Ap join_A } `{BCorr : TypeCorr B Bp join_B}
      `(f:A->B)  (fp:Ap->Bp) `{HP:@ParProp A Ap join_A ACorr P}:=
  { fun_corr : forall ap, P ap -> join_B (fp ap) =  f (join_A ap) }.

Class FunCorr2 
      `{ACorr : TypeCorr A Ap join_A} `{BCorr : TypeCorr B Bp join_B}
      `{CCorr : TypeCorr C Cp join_C} `(f:A->B->C)  (fp:Ap->Bp->Cp)
      `{HP:@Par2Prop A Ap join_A ACorr B Bp join_B BCorr P} :=
  {  fun_corr2: forall ap bp, par2_prop ap bp ->
                         join_C (fp ap bp) =  f (join_A ap) (join_B bp) }.

(** *** Instances: Combinations on Parallel Properties *)

#[export] Instance curry_par2prop
         `{HA:TypeCorr A Ap joinA} `{HB:TypeCorr B Bp joinB} (P:Ap->Bp->Prop)
         `{H:@Par2Prop A Ap joinA HA B Bp joinB HB P} :
  @ParProp (A*B) (Ap*Bp) (joinA × joinB) _ (prod_curry P) :=
  Build_ParProp _ (prod_curry P).

#[export] Instance pairing_prop
         `{HA: TypeCorr A Ap joinA} `{HB: TypeCorr B Bp joinB}
         `{HPA: @ParProp A Ap joinA HA Pa} `{HPB: @ParProp B Bp joinB HB Pb} :
  ParProp (A:=A*B) (prod_curry(fun x y=> and(Pa x)(Pb y))) := Build_ParProp _ _.

(** *** Instances: No Parallelization *)

#[export] Instance fc_nopar `(f:A->B) : FunCorr f f | 2000.
Proof. now constructor. Qed.

#[export] Instance fc2_nopar_and `(f:A->B->C): FunCorr2 f f (P:=fun(x:A)(y:B)=>True/\True) | 1999.
Proof. now constructor. Qed.

#[export] Instance fc2_nopar `(f:A->B->C) : FunCorr2 f f | 2000.
Proof. now constructor. Qed.

(** *** Instances: Self Correspondence of id, fst, snd *)

#[export] Instance fc_id `{ACorr : TypeCorr A Ap join_A} : FunCorr id id.
Proof. constructor; now intros ap. Qed.

#[export] Instance fc_fst
         `{ACorr : TypeCorr A Ap join_A}
         `{BCorr : TypeCorr B Bp join_B}
         `{HPA: @ParProp A Ap joinA HA Pa}
         `{HPB: @ParProp B Bp joinB Hb Pb} :
  @FunCorr (A*B) (Ap*Bp) _ _ _ Ap _ _  fst fst (prod_curry(fun x y=>(Pa x)/\(Pb y))) _ .
Proof.
  constructor; now intros.
Qed.

#[export] Instance fc_snd
         `{ACorr : TypeCorr A Ap join_A}
         `{BCorr : TypeCorr B Bp join_B}
         `{HPA: @ParProp A Ap joinA HA Pa}
         `{HPB: @ParProp B Bp joinB Hb Pb} :
  @FunCorr (A*B) (Ap*Bp) _ _ _ Bp _ _  snd snd (prod_curry(fun x y=>and(Pa x)(Pb y))) _ .
Proof.
  constructor; now intros ap.
Qed.

(** *** Instances: Correspondence of Tuplings of Correspondences *)

#[export] Instance fc_tupling_fc_fc
        `{ACorr : TypeCorr A Ap join_A}
        `{BCorr : TypeCorr B Bp join_B}
        `{CCorr : TypeCorr C Cp join_C}
        `{fCorr : @FunCorr A Ap join_A ACorr B Bp join_B BCorr f fp P HP}
        `{gCorr : @FunCorr A Ap join_A ACorr C Cp join_C CCorr g gp P HP} :
  FunCorr  (f △ g) (fp △ gp).
Proof.
  constructor; intros ap Hap; autounfold with sydpacc; simpl.
  erewrite @fun_corr with (f:=f) by (typeclasses eauto || auto).
  erewrite @fun_corr with (f:=g) by (typeclasses eauto || auto).
  trivial.
Qed.

(** *** Instances: Correspondence of Pairing of Correspondences *)

#[export] Instance fc_pairing_fc_fc
         `{ACorr : TypeCorr A Ap join_A}
         `{BCorr : TypeCorr B Bp join_B}
         `{CCorr : TypeCorr C Cp join_C}
         `{DCorr : TypeCorr D Dp join_D}
        `{fCorr : @FunCorr A Ap join_A ACorr C Cp join_C CCorr f fp Pa HPa}
        `{gCorr : @FunCorr B Bp join_B BCorr D Dp join_D DCorr g gp Pb HPb} :
  FunCorr (f × g) (fp × gp)(P:=prod_curry(fun x y=>and(Pa x)(Pb y))).
Proof.
  constructor; intros [ap bp] HH; autounfold with sydpacc; simpl.
  erewrite @fun_corr with (f:=f) by (typeclasses eauto || firstorder).
  erewrite @fun_corr with (f:=g) by (typeclasses eauto || firstorder).
  trivial.
Qed.

(** *** Instances: Correspondence of Curried Function Correspondence *)

#[export] Instance fc_prod_curry_fc2
        `{ACorr : TypeCorr A Ap join_A}
        `{BCorr : TypeCorr B Bp join_B}
        `{CCorr : TypeCorr C Cp join_C}
        `{fCorr : @FunCorr2 A Ap join_A ACorr B Bp join_B BCorr
                             C Cp join_C CCorr f fp P HP} :
  FunCorr (A:=A*B)(B:=C)
           (prod_curry f) (prod_curry fp) (P:=prod_curry P)
           (HP:=@curry_par2prop A Ap join_A ACorr B Bp _ _ P HP).
Proof.
  constructor; intros [ap1 ap2] H; autounfold with sydpacc; simpl.
  erewrite @fun_corr2 with (f:=f).
  - trivial.
  - typeclasses eauto.
  - apply H.
Qed.

(** *** Instances: Taking into Account Optimizations *)

#[export] Instance fc_opt1
         `{ACorr : TypeCorr A Ap join_A}
         `{BCorr : TypeCorr B Bp join_B}
         `{optim: @Opt A B f' f} 
         `{fCorrP : @FunCorr A Ap join_A ACorr B Bp join_B BCorr f fp P HP} :
  @FunCorr A Ap join_A ACorr B Bp join_B BCorr f' fp P HP.
Proof.
  constructor; intros ap Ha.
  rewrite @fun_corr with (ACorr:=ACorr)(BCorr:=BCorr)(f:=f)(P:=P)(HP:=HP)
    by (typeclasses eauto || auto).
  symmetry. apply opt_eq.
Defined.

#[export] Instance fc2p_opt2
         `{ACorr : TypeCorr A Ap join_A}
         `{BCorr : TypeCorr B Bp join_B}
         `{CCorr : TypeCorr C Cp join_C}
         `{optim: @Opt2 A B C f' f}          
         `{fCorr : @FunCorr2 A Ap join_A ACorr B Bp join_B BCorr C Cp join_C CCorr f fp H HP} :
  @FunCorr2 A Ap join_A ACorr B Bp join_B BCorr C Cp join_C CCorr f' fp H HP.
Proof.
  constructor; intros ap bp Hab.
  erewrite @fun_corr2 with (f:=f) by (typeclasses eauto || auto).
  symmetry. apply opt2_eq.
Defined.

(** *** Instances: Composition of Function Correspondence *)

Class EnsuresProp `(f:A->B)`(P:B->Prop) :=
  { ensures_prop: forall a:A, P(f a) }.

Class EnsuresProp2 `(f:A->B)`(P:A->B->Prop) :=
  { ensures_prop2: forall a, P a (f a) }.

#[export] Instance ensures_prop_true `(f:A->B) : EnsuresProp f (fun x=>True).
Proof. now constructor. Qed.

#[export] Instance ensures_prop2_true `(f:A->B) : EnsuresProp2 f (fun x y=>True).
Proof. now constructor. Qed.

#[export] Instance ensures_prop_pairing_true `(f:A->B*C) :
  EnsuresProp f (prod_curry(fun x y=>and True True)).
Proof. constructor; intro a; destruct (f a); simpl; auto. Qed.

#[export] Instance ensures_prop2_prod_curry `{E: EnsuresProp2 A B f P}:
  @EnsuresProp A (A * B) (id △ f) (prod_curry P).
Proof.
  constructor; autounfold with sydpacc; simpl.
  apply ensures_prop2.
Defined.

#[export] Instance ensures_prop_prod_curry_and_fst
         `{H: @EnsuresProp A (B*C) f (P ∘ fst)} :
  EnsuresProp f (prod_curry (fun x y=>P x /\ True)).
Proof.
  constructor; intro a; destruct (f a) as [b c] eqn:Hfa; simpl; split; auto.
  replace b with (fst(f a)) by now rewrite Hfa.
  apply H.
Qed.

#[export] Instance ensures_prop_prod_curry_and_snd
         `{H: @EnsuresProp A (B*C) f (P ∘ snd)} :
  EnsuresProp f (prod_curry (fun x y=>True /\ P y)).
Proof.
  constructor; intro a; destruct (f a) as [b c] eqn:Hfa; simpl; split; auto.
  replace c with (snd(f a)) by now rewrite Hfa.
  apply H.
Qed.

#[export] Instance fc_comp_fcensures
        `{ACorr : TypeCorr A Ap join_A}
        `{BCorr : TypeCorr B Bp join_B}
        `{CCorr : TypeCorr C Cp join_C}
        `{fCorr : @FunCorr A Ap join_A ACorr B Bp join_B BCorr f fp Pa HPa}
        `{gCorr : @FunCorr B Bp join_B BCorr C Cp join_C CCorr g gp Pb HPb}
        `{H: @EnsuresProp Ap Bp fp Pb } 
  : FunCorr (g ∘ f) (gp ∘ fp).
Proof.
  constructor; intros ap Ha; autounfold with sydpacc; simpl.
  erewrite <- @fun_corr with (f:=f) by (typeclasses eauto || auto).
  now erewrite <- @fun_corr with (f:=g)(fp:=gp)
    by (typeclasses eauto || auto || apply H).
Qed.

(** * Automatic Parallelization through Instance Resolution *)

Unset Implicit Arguments.
Definition parallel `(f:A->B)
           `{ACorr : TypeCorr A Ap join_A} `{BCorr : TypeCorr B Bp join_B}
           `{fCorr : @FunCorr A Ap join_A ACorr B Bp join_B BCorr f fp (fun x=>True) HP} :
  Ap -> Bp := fp.

#[export] Hint Unfold parallel : sydpacc.

Declare Reduction sydpacc := 
  cbv beta delta
      [parallel optimised_op optimised_f optimised_op_sig
                optimised_f_sig hom_to_map_reduce compose tupling of_img].

Close Scope sydpacc_scope.
