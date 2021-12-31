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
  Definition kL_one {A} (x:A) := 1.
  Definition kN_one {B} (x:B) := 1 .
  
  Open Scope sydpacc_scope.
  
  Definition spec_mapone {A B} : BTree.t A B -> BTree.t N N :=
    BTree.map kL_one kN_one.

  Typeclasses eauto := (bfs). 

  Definition mapone {A B} : PLTree A B -> PLTree N N:=
    Eval sydpacc in
    parallel(spec_mapone).

  Close Scope sydpacc_scope.
  
End Make.

Close Scope N_scope.
