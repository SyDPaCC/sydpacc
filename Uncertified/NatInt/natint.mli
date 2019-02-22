(** Conversion between OCaml [int] type and Coq [nat] type. *)
type nat = O | S of nat

(** Converts an [int] to a [nat]. *) 
val nat_of_int: int -> nat

exception NatTooBig
    
(** Converts a natural number to an int, raises [NatTooBig] is the
    natural number is greater that [max_int]. *)
val int_of_nat: nat -> int

(** Printing a [nat] as it is constructed. *)
val string_of_nat: nat -> string

(** Printing a [nat] in decimal notation. *)
val string_of_nat': nat -> string 
