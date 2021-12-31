(** * Parallelization of the Maximum Prefix Sum Application *)

Require Import SyDPaCC.Core.Bmf SyDPaCC.Core.Parallelization.
Require Import SyDPaCC.Applications.Mps.

Require Import SyDPaCC.Bsml.Model.Core SyDPaCC.Bsml.Model.Pid 
        SyDPaCC.Bsml.DataStructures.DistributedList
        SyDPaCC.Bsml.DataStructures.ReplicatedValue
        SyDPaCC.Bsml.Skeletons.StdLib
        SyDPaCC.Bsml.Skeletons.MapReduce.

Open Scope sydpacc_scope.

Module Make (Import Bsml: Core.BSML)(N: Number).

  Module Pid       := Pid.Make Bsml.Bsp.
  Module StdLib    := StdLib.Make Bsml Pid.
  Module Import ParList   := DistributedList.C Bsml Pid.
  Module Import ReplPar   := ReplicatedValue.C Bsml Pid.
  Module Import MapReduce := MapReduce.Make Bsml Pid StdLib ParList ReplPar.
  Module Import Mps := SyDPaCC.Applications.Mps.Make N.

  (** ** Version where the result is a scalar *)

  Definition mr_mps := Eval sydpacc in hom_to_map_reduce Mps.ms_spec.
  
  Definition par_ms : par(list N.t) -> img Mps.ms_spec :=
    Eval sydpacc in 
      parallel (hom_to_map_reduce Mps.ms_spec).

  Definition par_mps : par(list N.t) -> N.t :=
    Eval sydpacc in
      fst ∘ of_img ∘ par_ms.

  
  (** ** Version where the result is a parallel vector *)
  Definition par_ms' := Eval sydpacc in 
      parallel (hom_to_map_reduce Mps.ms_spec).

  Definition par_mps' : par(list N.t) -> par N.t :=
    Eval sydpacc in
      (apply(mkpar(fun _=>fst ∘ of_img))) ∘ (@proj1_sig _ _) ∘ par_ms'.
  
End Make.

Close Scope sydpacc_scope.
