Require Import SyDPaCC.Core.Bmf.
Require Import SyDPaCC.Core.Parallelization.

Generalizable All Variables.

Open Scope sydpacc_scope.

(** * Composition of Type Correspondences *)

#[export] Instance tc_corr_composition
         `{TypeCorr typA typB joinAB}
         `{TypeCorr typB typC joinBC} :
  @TypeCorr typA typC (joinAB ∘ joinBC).
Proof.
  repeat constructor; unfold compose; intros a.
  assert(exists x, joinAB x = a) as [ xB HB] by apply surjective.
  assert(exists x, joinBC x = xB) as [ xC HC] by apply surjective.
  eexists; rewrite HC; auto.
Defined.

(** * Vertical Composition of Function Correspondences *)

#[export] Instance fc_vertical_comp_fcensures
        `{ACorr12: TypeCorr A1 A2 join_A12}
        `{BCorr12: TypeCorr B1 B2 join_B12}
        `{ACorr23: TypeCorr A2 A3 join_A23}
        `{BCorr23: TypeCorr B2 B3 join_B23}
        `{fCorr12: @FunCorr A1 A2 join_A12 ACorr12 B1 B2 join_B12 BCorr12 f1 f2 Pa12 HPa12}
        `{fCorr23: @FunCorr A2 A3 join_A23 ACorr23 B2 B3 join_B23 BCorr23 f2 f3 Pa23 HPa23}
        {H: @EnsuresProp _ _ join_A23 Pa12 }
  : @FunCorr _ _ _ _ _ _ _ _ f1 f3 _ (@Build_ParProp _ _ (join_A12 ∘ join_A23) _ Pa23).
Proof.
  constructor; intros a3 Ha3; autounfold with sydpacc; simpl.
  erewrite <- @fun_corr with (f:=f1)
    by (typeclasses eauto || eauto using ensures_prop).
  erewrite <- @fun_corr with (f:=f2)
    by (typeclasses eauto || eauto using ensures_prop).
  trivial.
Defined.

#[export] Instance fc_vertical_comp_fcensures_toseq
        `{ACorr12: TypeCorr A1 A2 join_A12}
        `{ACorr23: TypeCorr A2 A3 join_A23}
        `{fCorr12: @FunCorr A1 A2 join_A12 ACorr12 B B (fun x=>x) BCorr f1 f2 Pa12 HPa12}
        `{fCorr23: @FunCorr A2 A3 join_A23 ACorr23 B B (fun x=>x) BCorr f2 f3 Pa23 HPa23}
        {H: @EnsuresProp _ _ join_A23 Pa12 }
  : @FunCorr _ _ _ _ _ _ _ _ f1 f3 _ (@Build_ParProp _ _ (join_A12 ∘ join_A23) _ Pa23).
Proof.
  constructor; intros a3 Ha3; autounfold with sydpacc; simpl.
  erewrite <- @fun_corr with (f:=f1)
    by (typeclasses eauto || eauto using ensures_prop).
  erewrite <- @fun_corr with (f:=f2)
    by (typeclasses eauto || eauto using ensures_prop).
  trivial.
Defined.

Close Scope sydpacc_scope.


