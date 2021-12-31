(** Conversion between OCaml [int] type and Coq [N] type. *)

open BinNums

(* Conversions are cached. *)
let int_nat_table = Hashtbl.create 997
let nat_int_table = Hashtbl.create 997

let rec positive_of_int_compute (i:int) : positive =
  match i with
  | 1 -> Coq_xH
  | n when n>1 ->
     let n' = positive_of_int_compute (i/2) in
     if n mod 2 = 0
     then Coq_xO n'
     else Coq_xI n'
  | _ -> failwith "cannot convert a negative int to positive"
				   
let rec n_of_int_compute (i:int) : coq_N = 
  match i with
  | 0 -> N0
  | n when n>0 -> Npos(positive_of_int_compute i)
  | _ -> failwith "cannot convert a strictly negative int to Coq_N"
  

let rec int_of_positive_compute (n:positive) : int =
  match n with
  | Coq_xH -> 1
  | Coq_xI n ->
     1 + 2*(int_of_positive_compute n)
  | Coq_xO n ->
     2*(int_of_positive_compute n)
	    
let int_of_n_compute (n:coq_N) : int =
  match n with
  | N0 -> 0
  | Npos n ->
     int_of_positive_compute n
     
let n_of_int (i:int) :  coq_N =
  try 
    Hashtbl.find int_nat_table i
  with Not_found ->
    let nat = n_of_int_compute i in
    Hashtbl.add int_nat_table i nat; nat

let int_of_n (n:coq_N) : int =
  try 
    Hashtbl.find nat_int_table n
  with Not_found ->
    let i = int_of_n_compute n in
    Hashtbl.add nat_int_table n i; i

