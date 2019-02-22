(** Conversion between OCaml [int] type and Coq [nat] type. *)

type nat = O | S of nat

(* Conversions are cached. *)
let int_nat_table = Hashtbl.create 997
let nat_int_table = Hashtbl.create 997

let nat_of_int_compute (i:int) : nat = 
  let rec aux i n = 
    if i <= 0 
    then n
    else aux (i-1) (S n) in
  aux i O

exception NatTooBig

let int_of_nat_compute (n:nat) : int = 
  let rec aux n i = 
    if i >= max_int
    then raise NatTooBig
    else
      match n with 
      | O -> i
      | S n -> aux n (i+1) in
  aux n 0
  
let nat_of_int (i:int) : nat =
  try 
    Hashtbl.find int_nat_table i
  with Not_found ->
    let nat = nat_of_int_compute i in
    Hashtbl.add int_nat_table i nat; nat

let int_of_nat (n:nat) : int =
  try 
    Hashtbl.find nat_int_table n
  with Not_found ->
    let i = int_of_nat_compute n in
    Hashtbl.add nat_int_table n i; i

(** Printing a [nat] as it is constructed. *)
let string_of_nat (n:nat) : string =
  let rec aux s = function
    | O   -> s
    | S n -> aux ("S"^s) n in
  aux "O" n

(** Printing a [nat] in decimal notation. *)
let string_of_nat' (n:nat) : string =
  "n"^(string_of_int (int_of_nat n))
