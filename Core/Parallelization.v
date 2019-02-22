Require Import SyDPaCC.Core.Bmf.
Require Import Coq.Lists.List. Import ListNotations.
Generalizable All Variables.
Set Implicit Arguments.

Open Scope sydpacc_scope.

(** * Classes for Automatic Parallelization *)

Class Surjective A B (f:A->B) :=
  {
    surjective :  forall y : B,  exists x : A,  f x = y 
  }.

(** ** Type Correspondance *)

Class TypeCorr (seq_type:Type) (par_type:Type) (join:par_type->seq_type) :=
  {
    type_corr :> Surjective join
  }.

(** *** Instances: Composition of Type Correspondance *)

Instance tc_nopar (A:Type) : TypeCorr (fun x:A=>x) | 200.
Proof.
  repeat constructor; intro; eexists; reflexivity.
Qed.

Instance tc_corr_pairs
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


(** ** Function Correspondance *)

Class ParProp `{HA:TypeCorr A Ap} (P:Ap->Prop) :=
  {
    par_prop := P
  }.

Class Par2Prop `{HA:TypeCorr A Ap} `{HB:TypeCorr B Bp} (P:Ap->Bp->Prop) :=
  {
    par2_prop := P
  }.

Class FunCorr
      `{ACorr : TypeCorr A Ap join_A}
      `{BCorr : TypeCorr B Bp join_B}
      (f:A->B)  (fp:Ap->Bp) :=
  { 
    fun_corr : forall ap,  join_B (fp ap) =  f (join_A ap)
  }.

Class FunCorrP
      `{ACorr : TypeCorr A Ap join_A }
      `{BCorr : TypeCorr B Bp join_B}
      `(f:A->B)  (fp:Ap->Bp) `{HP:@ParProp A Ap join_A ACorr P}:=
  { 
    fun_corr_p : forall ap,
      P ap -> 
      join_B (fp ap) =  f (join_A ap)
  }.

Class FunCorr2P 
      `{ACorr : TypeCorr A Ap join_A}
      `{BCorr : TypeCorr B Bp join_B}
      `{CCorr : TypeCorr C Cp join_C}
      `(f:A->B->C)  (fp:Ap->Bp->Cp)
      `{HP:@Par2Prop A Ap join_A ACorr B Bp join_B BCorr P} :=
  { 
    fun_corr2_p: forall ap bp,
      par2_prop ap bp -> join_C (fp ap bp) =  f (join_A ap) (join_B bp)
  }.

Class FunCorr2 
      `{ACorr : TypeCorr A Ap join_A}
      `{BCorr : TypeCorr B Bp join_B}
      `{CCorr : TypeCorr C Cp join_C}
      `(f:A->B->C)  (fp:Ap->Bp->Cp) :=
  { 
    fun_corr2: forall ap bp,
      join_C (fp ap bp) =  f (join_A ap) (join_B bp)
  }.

(** *** Instances: Combinations on Parallel Properties *)

Instance curry_par2prop
         `{HA:TypeCorr A Ap joinA} `{HB:TypeCorr B Bp joinB} (P:Ap->Bp->Prop)
         `{H:@Par2Prop A Ap joinA HA B Bp joinB HB P} :
  @ParProp (A*B) (Ap*Bp) (joinA × joinB) _ (prod_curry P) :=
  Build_ParProp _ (prod_curry P).

Instance pairing_prop
         `{HA: TypeCorr A Ap joinA} `{HB: TypeCorr B Bp joinB}
         `{HPA: @ParProp A Ap joinA HA Pa} `{HPB: @ParProp B Bp joinB HB Pb} :
  ParProp (A:=A*B) ((prod_curry and)∘ (Pa × Pb)) := Build_ParProp _ _.

Instance pairing_prop_left
         `{HA: TypeCorr A Ap joinA}   
         `{HB: TypeCorr B Bp joinB}
         `{HPA: @ParProp A Ap joinA HA Pa} :
  ParProp (A:=A*B) (Pa ∘ fst) := Build_ParProp _ (Pa ∘ fst).

Instance pairing_prop_right
         `{HA: TypeCorr A Ap joinA}   
         `{HB: TypeCorr B Bp joinB}
         `{HPB: @ParProp B Bp joinB HB Pb} :
  ParProp (A:=A*B) (Pb ∘ snd) := Build_ParProp _ _.

(** *** Instances: Self Correspondance of id, fst, snd *)

Instance fc_id
         `{ACorr : TypeCorr A Ap join_A} : FunCorr id id.
Proof.
  constructor; now intros ap.
Qed.

Instance fc_fst_par_par
         `{ACorr : TypeCorr A Ap join_A}
         `{BCorr : TypeCorr B Bp join_B}
  : @FunCorr (A*B) (Ap*Bp)_ _ _ Ap _ _  fst fst.
Proof.
  constructor; now intros ap.
Qed.

Instance fc_fst_seq_par
         A
         `{BCorr : TypeCorr B Bp join_B}
  : @FunCorr (A*B)%type (A*Bp)%type _ _ A A _ _ fst fst.
Proof.
  constructor; now intros ap.
Qed.

Instance fc_fst_par_seq
         `{ACorr : TypeCorr A Ap join_A}
         B
  : @FunCorr (A*B) (Ap*B) _ _ _ Ap _ _ fst fst.
Proof.
  constructor; now intros ap.
Qed.

Instance fc_snd_par_par
         `{ACorr : TypeCorr A Ap join_A}
         `{BCorr : TypeCorr B Bp join_B}
  : @FunCorr (A*B) (Ap*Bp) _ _ _ Bp _ _  snd snd.
Proof.
  constructor; now intros ap.
Qed.

Instance fc_snd_seq_par
         A
         `{BCorr : TypeCorr B Bp join_B}
  : @FunCorr (A*B) (A*Bp) _ _ _ Bp _ _  snd snd.
Proof.
  constructor; now intros ap.
Qed.

Instance fc_snd_par_seq
         `{ACorr : TypeCorr A Ap join_A}
         B
  : @FunCorr (A*B) (Ap*B) _ _ B B _ _ snd snd.
Proof.
  constructor; now intros ap.
Qed.

(** *** Instances: Correspondance of Tuplings of Correspondances *)

Instance fc_tupling_fc_fc
        `{ACorr : TypeCorr A Ap join_A}
        `{BCorr : TypeCorr B Bp join_B}
        `{CCorr : TypeCorr C Cp join_C}
        `{fCorr : @FunCorr A Ap join_A ACorr B Bp join_B BCorr f fp}
        `{gCorr : @FunCorr A Ap join_A ACorr C Cp join_C CCorr g gp} :
  FunCorr  (f △ g) (fp △ gp).
Proof.
  constructor; intro ap; autounfold; simpl.
  erewrite @fun_corr with (f:=f) by typeclasses eauto.
  erewrite @fun_corr with (f:=g) by typeclasses eauto.
  trivial.
Qed.

(** *** Instances: Correspondance of Pairing of Correspondances *)


Instance fc_pairing_fc_seq
        `{ACorr : TypeCorr A Ap join_A}
        `{BCorr : TypeCorr B Bp join_B}
        C D
        `{fCorr : @FunCorr A Ap join_A ACorr B Bp join_B BCorr f fp}
        `(g :C ->D) :
  FunCorr (f × g) (fp × g).
Proof.
  constructor; intro ap; autounfold; simpl.
  now erewrite @fun_corr with (f:=f) by typeclasses eauto.
Qed.

Instance fc_pairing_seq_fc
         A B
        `{CCorr : TypeCorr C Cp join_C}
        `{DCorr : TypeCorr D Dp join_D}
        `(f: A -> B)
        `{gCorr : @FunCorr C Cp join_C CCorr D Dp join_D DCorr g gp} :
  FunCorr (f × g) (f × gp).
Proof.
  constructor; intro ap; autounfold; simpl.
  now erewrite @fun_corr with (f:=g) by typeclasses eauto.
Qed.

Instance fc_pairing_fc_fc
        `{ACorr : TypeCorr A Ap join_A}
        `{BCorr : TypeCorr B Bp join_B}
        `{CCorr : TypeCorr C Cp join_C}
        `{DCorr : TypeCorr D Dp join_D}
        `{fCorr : @FunCorr A Ap join_A ACorr B Bp join_B BCorr f fp}
        `{gCorr : @FunCorr C Cp join_C CCorr D Dp join_D DCorr g gp} :
  FunCorr (f × g) (fp × gp).
Proof.
  constructor; intro ap; autounfold; simpl.
  erewrite @fun_corr with (f:=f) by typeclasses eauto.
  erewrite @fun_corr with (f:=g) by typeclasses eauto.
  trivial.
Qed.

Instance fcp_pairing_fcp_seq
         `{ACorr : TypeCorr A Ap join_A}
         B
         `{CCorr : TypeCorr C Cp join_C}
         D
        `{fCorr : @FunCorrP A Ap join_A ACorr C Cp join_C CCorr  f fp P HP}
        `(g : B->D) :
  FunCorrP (f × g) (fp × g) (P:=P ∘ fst).
Proof.
  constructor; intros ap Hap. autounfold; simpl.
  now erewrite @fun_corr_p with (f:=f) by
      (typeclasses eauto || destruct ap; simpl; apply Hap).
Qed.

Instance fcp_pairing_seq_fcp
         `{ACorr : TypeCorr A Ap join_A}
         B
         `{CCorr : TypeCorr C Cp join_C}
         D
        `{fCorr : @FunCorrP A Ap join_A ACorr C Cp join_C CCorr  f fp P HP}
        `(g : B->D) :
  FunCorrP (g × f) (g × fp).
Proof.
  constructor; intros ap Hap; autounfold; simpl.
  now erewrite @fun_corr_p with (f:=f) by
      (typeclasses eauto || destruct ap; simpl; apply Hap).
Qed.

Instance fcp_pairing_fcp_fcp
         `{ACorr : TypeCorr A Ap join_A}
         `{BCorr : TypeCorr B Bp join_B}
         `{CCorr : TypeCorr C Cp join_C}
         `{DCorr : TypeCorr D Dp join_D}
        `{fCorr : @FunCorrP A Ap join_A ACorr C Cp join_C CCorr f fp Pa HPa}
        `{gCorr : @FunCorrP B Bp join_B BCorr D Dp join_D DCorr g gp Pb HPb} :
  FunCorrP (f × g) (fp × gp)(P:=(prod_curry and)∘ (Pa × Pb)).
Proof.
  constructor; intros [ap bp] HH; autounfold; simpl.
  erewrite @fun_corr_p with (f:=f) by (typeclasses eauto || firstorder).
  erewrite @fun_corr_p with (f:=g) by (typeclasses eauto || firstorder).
  trivial.
Qed.

(** *** Instances: Correspondance of Curried Function Correspondance *)

Instance fcp_prod_curry_fc2p
        `{ACorr : TypeCorr A Ap join_A}
        `{BCorr : TypeCorr B Bp join_B}
        `{CCorr : TypeCorr C Cp join_C}
        `{fCorr : @FunCorr2P A Ap join_A ACorr B Bp join_B BCorr
                             C Cp join_C CCorr f fp P HP} :
  FunCorrP (A:=A*B)(B:=C)
           (prod_curry f) (prod_curry fp) (P:=prod_curry P)
           (HP:=@curry_par2prop A Ap join_A ACorr B Bp _ _ P HP).
Proof.
  constructor; intros [ap1 ap2] H; autounfold; simpl.
  erewrite @fun_corr2_p with (f:=f).
  - trivial.
  - typeclasses eauto.
  - apply H.
Qed.

Instance fc_prod_curry_fc2
        `{ACorr : TypeCorr A Ap join_A}
        `{BCorr : TypeCorr B Bp join_B}
        `{CCorr : TypeCorr C Cp join_C}
        `{fCorr : @FunCorr2 A Ap join_A ACorr B Bp join_B BCorr
                            C Cp join_C CCorr f fp} :
  FunCorr (prod_curry f) (prod_curry fp).
Proof.
  constructor; intros [ap1 ap2]; autounfold; simpl.
  now erewrite @fun_corr2 with (f:=f) by typeclasses eauto.
Qed.


(** *** Instances: Compositions of Function Correspondance *)

Instance fc_comp_fc
        `{ACorr : TypeCorr A Ap join_A}
        `{BCorr : TypeCorr B Bp join_B}
        `{CCorr : TypeCorr C Cp join_C}
        `{fCorr : @FunCorr A Ap join_A ACorr B Bp join_B BCorr f fp}
        `{gCorr : @FunCorr B Bp join_B BCorr C Cp join_C CCorr g gp} :
  FunCorr (compose g f) (compose gp fp).
Proof.
  constructor; intros; autounfold.
  erewrite <- @fun_corr with (f:=f) by typeclasses eauto.
  now erewrite <- @fun_corr with (f:=g) by typeclasses eauto.
Qed.

Instance fc_comp_fcp
        `{ACorr : TypeCorr A Ap join_A}
        `{BCorr : TypeCorr B Bp join_B}
        `{CCorr : TypeCorr C Cp join_C}
        `{fCorr : @FunCorr A Ap join_A ACorr B Bp join_B BCorr f fp}
        `{gCorr : @FunCorrP B Bp join_B BCorr C Cp join_C CCorr g gp P HP}
        `{H: forall ap, P (fp ap) }
  : FunCorr (g ∘ f) (gp ∘ fp).
Proof.
  constructor; intro ap; autounfold; simpl.
  erewrite <- @fun_corr with (f:=f) by typeclasses eauto.
  erewrite <- @fun_corr_p with (f:=g)(fp:=gp).
  - trivial.
  - typeclasses eauto.
  - apply H.
Qed.

(** * Automatic Parallelization through Instance Resolution *)

Unset Implicit Arguments.
Definition parallel `(f:A->B)
           `{ACorr : TypeCorr A Ap join_A} `{BCorr : TypeCorr B Bp join_B}
           `{fCorr : @FunCorr A Ap join_A ACorr B Bp join_B BCorr f fp} :
  Ap -> Bp := fp.

Hint Unfold parallel.

Declare Reduction sydpacc := 
  cbv beta delta
      [parallel optimised_op optimised_f optimised_op_sig
                optimised_f_sig hom_to_map_reduce compose tupling of_img].

Close Scope sydpacc_scope.