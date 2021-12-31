open BTree
open LTree
open String
open BinNums
open BsmlWrapperN
open List1

let filename =  Sys.argv.(1) 
let filename_bt = "../"^filename ^ ".btree" 
let filename_type = "../"^filename ^ ".type" 

let np = 
	try int_of_string (Sys.argv.(2)) 
	with _ -> 1

let verb = 
	try bool_of_string (Sys.argv.(4)) 
	with _ -> false


let usage () = 
  begin
    print_string ("Usage: "^(Sys.argv.(0))^" filename nbfiles m [true|false]\n");
    exit 1;
  end	

(* Make strings *)
let repeat_c s n=
  let rec aux n acc =
  match n with
  | 0 -> acc
  | n -> aux (n-1) (acc^s)
in aux n ""

(*
let string_of_tree t sta stb=
  let rec aux t h =
    match t with
    | Leaf a -> (repeat_c "\t" h) ^ "Leaf " ^ (sta a) ^ "\n"
    | Node (b,l,r) -> (repeat_c "\t" h) ^ "Node " ^ (stb b) ^ "\n" ^ (aux l (h+1)) ^ "\n" ^ (aux r (h+1))
in aux t 0

let string_of_val sA sB v =
	match v with
	| Le x -> "Le:"^(sA x)
	| No x -> "No:"^(sB x)
	| Cr x ->  "Cr:"^(sB x)

let string_of_segment sA sB l =
	let rec aux l acc =
	match l with
	| [] -> acc^"]"
	| [v] -> acc^(string_of_val sA sB v)^"]" 	
	| v :: vs -> aux vs (acc^(string_of_val sA sB v)^",")
in aux l "["

let string_of_segments sA sB l =
	let rec aux l acc =
	match l with
	| [] -> acc^"]"
	| [s] -> acc^(string_of_segment sA sB s)^"]" 	
	| s :: ls -> aux ls (acc^(string_of_segment sA sB s))^";"
	in aux l "["
 *)

(* Separate a list of elements *)
 let rec take_aux n xs acc =
  if n <= 0
  then List.rev acc
  else match xs with 
       | [] -> List.rev acc
       | x::xs -> take_aux (n-1) xs (x::acc)

let take n xs = take_aux n xs []

let rec drop n xs =
  if n<=0
  then xs
  else
    match xs with
    | [] -> []
    | h::t -> drop (n-1) t


let rem size = size mod np 

let lsz size = size / np 

let drops pid size= 
	pid * (lsz size) + if pid < (rem size) then pid else (rem size)

let takes pid size= 
	(lsz size) + if pid < (rem size) then 1 else 0 

let length' l = List.fold_left (fun a _ -> a+1) 0 l



let rec separate_file l np filename size=
	let rec aux n  =
	match n with
	| 0 -> ();
	| p -> 
		let id = (np - p) in
		let oc = open_out (filename^"."^(string_of_int id)) in
		let to_drop = (drops (np - p) size) in
		let to_take = (takes id size) in
		let sub1 = (drop to_drop l) in
		let sub = take to_take sub1 in
		
 		let nsplit = string_of_int id in
		let nelem = string_of_int (List.fold_left (+) 0 (List1.map' length' sub)) in  
		let nsegs = string_of_int (length' sub) in 
		
		if verb then 
			print_string (Sys.argv.(2) ^ "\t" ^ Sys.argv.(3) ^ "\t" ^ nsegs ^ "\t" ^ nelem ^"\n" );
		Marshal.to_channel oc sub [];
		aux (p-1) 
in aux np 


(* Main *)
let m size =
  Nint.n_of_int(int_of_float(2. *. sqrt(float size)))

let _ =
	let bt = Marshal.from_channel (open_in filename_bt) in		
	let size_bt = BTree.size bt in
	let size_int = Nint.int_of_n size_bt in
	let m_i = 
		try 
			let read_m = int_of_string (Sys.argv.(3)) in
			Nint.n_of_int read_m
		with _ -> (m size_int)
	in
	let raw_segs = serialization bt m_i in
	let filename_lt = "../"^filename ^ "_"^(string_of_int np)^".ltree" in
	Marshal.to_channel (open_out filename_lt) raw_segs [];
	if verb then 
			print_string ("procs" ^ "\t" ^ "m" ^ "\t" ^ "nb segs" ^ "\t" ^ "nb elemts" ^ "\n" );
	separate_file raw_segs np filename_lt (List.length raw_segs)


