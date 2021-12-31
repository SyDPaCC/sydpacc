Require Import Coq.Logic.Eqdep_dec Arith NArith.

Module Types.

  Module Bool. 
    Definition U := bool. 
    Lemma eq_dec : forall x y:U, {x = y} + {x <> y}. 
      decide equality.
    Qed.
  End Bool.
  
  Module Nat.
    Definition U := nat.
    Definition eq_dec := eq_nat_dec.
  End Nat.

  Module N.
    Definition U:=N.
    Definition eq_dec := N.eq_dec.
  End N.
End Types.

Module Bool := DecidableEqDep Types.Bool.
Module Nat := DecidableEqDep Types.Nat.
Module N := DecidableEqDep Types.N.