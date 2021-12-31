Require Import NArith.

Generalizable All Variables.

Definition lift `(f:A->B) : option A -> option B :=
  fun x => match x with
        | Some v => Some(f v)
        | None => None
        end.

Definition decr :=
  lift (fun x => (x - 1)%N).

Definition incr :=
  lift (fun x => (x + 1)%N).
