From SyDPaCC.Tree Require Import
     Skeletons Closure BTree LTree.
From SyDPaCC.Bsml Require Import Model.Core Model.Pid Model.Sequential Skeletons.StdLib.
Require Import Lia NArith.
From SyDPaCC.Core Require Import Bmf Parallelization.

Open Scope sydpacc_scope.
Open Scope N_scope.

(** * Functions for the Application of reduce *)
Definition k_c: (N * N * N) -> N := fun t => match t with (a,b,c) => a + b + c end.
Definition phi_c : N -> N := fun x => x.
Definition psiN_c : (N * N * N) -> N := fun t => match t with (a,b,c) => a + b + c end.
Definition psiL_c : (N * N * N) -> N := fun t => match t with (a,b,c) => a + b + c end.
Definition psiR_c : (N * N * N) -> N := fun t => match t with (a,b,c) => a + b + c end.

#[local] Instance sum_closure : ClosureU k_c phi_c psiN_c psiL_c psiR_c.
Proof.
  constructor.
  split.
  + intros l b r. unfold k_c, psiN_c. unfold phi_c. reflexivity.
  + split.
    ++ intros x l y b r. unfold psiN_c, psiL_c.
       lia.
    ++ intros x l y b r. unfold psiN_c, psiR_c.
       lia.
Qed.

Definition spec_sumvalues: BTree.t N N -> option N :=
  Some  ∘ (BTree.reduce k_c).

(** * The Parallel Application *)

Module Make (Import Bsml : SyDPaCC.Bsml.Model.Core.BSML).

  Module Pid := Pid.Make Bsml.Bsp.
  Module StdLib := StdLib.Make Bsml Pid.
  Module Import Skel := Tree.Skeletons.Make Bsml.
  
  Typeclasses eauto := (bfs).
  
  Definition sumvalues:
    Skel.PLTree N N -> option N :=
    Eval sydpacc in
    parallel(spec_sumvalues).

End Make.
 
Close Scope sydpacc_scope.
Close Scope N_scope.
 
