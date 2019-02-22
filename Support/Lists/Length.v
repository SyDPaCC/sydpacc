Require Import Coq.Lists.List Arith Omega.

(** * Hints and a tactic for [List.length] *)

Hint Rewrite map_length app_length seq_length combine_length : length.
 
Ltac length :=
  repeat (simpl; autorewrite with length; simpl); auto with arith; try ring; try omega.



