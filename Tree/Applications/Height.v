From SyDPaCC.Tree Require Import
     Skeletons Closure BTree.
From SyDPaCC.Bsml Require Import Model.Core Model.Pid Skeletons.StdLib.
From SyDPaCC.Core Require Import Bmf Parallelization.
Require Import Lia NArith.

Open Scope N_scope.

Module Make (Import Bsml : SyDPaCC.Bsml.Model.Core.BSML).

  Module Pid := Pid.Make Bsml.Bsp.
  Module StdLib := StdLib.Make Bsml Pid.
  Module Import Skel := Tree.Skeletons.Make Bsml.

  (* Set functions for the application of map *)
  Definition kL_h {A} (x:A) := 1.
  Definition kN_h {B} (x:B) := exist _ 1 (eq_refl 1) .
  
  (* Set functions for the application of reduce *)
  Definition k_h : (N * {x : N | 1 = x} * N) -> N := fun t => match t with (l,b,r) => 1 + (N.max l r) end.
  Definition phi_h : {x : N | 1 = x} -> (N * N) := fun x => (0, (proj1_sig x)).
  Definition psiN_h : (N * (N * N) * N) -> N := fun t =>
                                                 match t with
                                                 | (l,(b1,b2),r) => N.max b1 (N.max (b2 + l) (b2 + r))
                                                 end.
  Definition psiL_h : (N * N) * (N * N) * N -> (N * N) :=
    fun t =>
      match t with
      | ((l1, l2),(b1,b2), r) => ((N.max b1 (N.max (b2 + l1) (b2 + r))), b2 + l2)
      end.
  Definition psiR_h : N * (N * N) * (N * N) -> (N * N) :=
    fun t =>
      match t with
      | (l, (b1, b2), (r1,r2)) => ((N.max b1 (N.max (b2 + l) (b2 + r1))), b2 + r2)
      end.

  #[local] Instance h_closure : ClosureU k_h phi_h psiN_h psiL_h psiR_h.
  Proof.
    constructor. 
    split.
    - intros l b r. unfold psiN_h, phi_h, k_h.
      rewrite N.add_max_distr_l, N.max_0_l.
      destruct b as [b Hb]. subst. trivial.
    - unfold psiN_h, psiL_h, psiR_h, phi_h, k_h. split.
      + intros x l y b r;
          destruct b as [b1 b2]; destruct l as [l1 l2].
        lia.
      + intros x l y b r;
          destruct b as [b1 b2]; destruct r as [r1 r2].
        lia.
  Qed. 

  Open Scope sydpacc_scope.
  
  Definition spec_height {A B} : BTree.t A B -> option N :=
    (Some ∘ (BTree.reduce k_h)) ∘ (BTree.map kL_h kN_h).

  Typeclasses eauto := (bfs).

  Definition height {A B} : PLTree A B -> option N :=
    Eval sydpacc in
    parallel(spec_height).

  Close Scope sydpacc_scope.
  
End Make.

Close Scope N_scope.
