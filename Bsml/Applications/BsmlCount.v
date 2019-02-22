(** * Parallelization of the Maximum Prefix Sum Application *)

Require Import SyDPaCC.Core.Bmf SyDPaCC.Core.Parallelization.
Require Import SyDPaCC.Applications.Count.

Require SyDPaCC.Bsml.Model.Core SyDPaCC.Bsml.Model.Pid 
        SyDPaCC.Bsml.DataStructures.DistributedList
        SyDPaCC.Bsml.DataStructures.ReplicatedValue
        SyDPaCC.Bsml.Skeletons.StdLib
        SyDPaCC.Bsml.Skeletons.MapReduce.

Set Implicit Arguments.

Open Scope sydpacc_scope.

Module Make (Import Bsml: Core.BSML).

  Module Pid       := Pid.Make Bsml.Bsp.
  Module ParList   := DistributedList.C Bsml Pid.
  Module ReplPar   := ReplicatedValue.C Bsml Pid.
  Module StdLib    := StdLib.Make Bsml Pid.
  Module MapReduce := MapReduce.Make Bsml Pid StdLib ParList ReplPar.

  Section Count.

    Variable A : Type.
    Variable predicate : { pred: A -> bool & { a : A | pred a = true} }.

    (** ** Version where the result is a scalar *)

    Definition par_count_img : par(list A) -> img (count_spec predicate) :=
      Eval sydpacc in 
        parallel (hom_to_map_reduce (count_spec predicate)).

    Definition par_count : par(list A) -> nat :=
      Eval sydpacc in
        of_img ∘ par_count_img.

    (** ** Version where the result is a parallel vector *)
    Definition par_count_img' :=
      Eval sydpacc in 
        parallel (hom_to_map_reduce (count_spec predicate)).

    Definition par_count' : par(list A) -> par nat :=
      Eval sydpacc in
        (StdLib.parfun of_img) ∘ (@proj1_sig _ _) ∘ par_count_img'.   
    
  End Count.

End Make.

Close Scope sydpacc_scope.