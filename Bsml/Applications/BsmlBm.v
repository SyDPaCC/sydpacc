(** * Parallelization of the Bracket Matching Application *)
Require Import NArith Lia.
From SyDPaCC.Core Require Import Bmf Diffusion Parallelization.
Require Import SyDPaCC.Support.NList.
From SyDPaCC.Bsml Require  Model.Core Model.Pid
     DataStructures.DistributedList
     Skeletons.StdLib Skeletons.Accumulate.
Require Import SyDPaCC.Applications.BracketMatching.

Open Scope sydpacc_scope.
Open Scope N_scope.

Module Make (Import Bsml: Core.BSML)(Char: CHAR).

  Module Pid       := Pid.Make Bsml.Bsp.
  Module StdLib    := StdLib.Make Bsml Pid.
  Module Import ParList   := DistributedList.C Bsml Pid.
  Module Import ParVect   := DistributedVector.C Bsml Pid.
  Module Import Accumulate := Accumulate.Make Bsml Pid StdLib ParList ParVect.
  Module BM := SyDPaCC.Applications.BracketMatching.Make Char. Include BM.

  Definition par_bm (s:list Char.t) : par(list Char.t) -> bool :=
    Eval sydpacc in
      parallel (bm_spec s).

End Make.

Close Scope sydpacc_scope.
Close Scope N_scope.
