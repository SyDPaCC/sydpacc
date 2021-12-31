open BTree
open String
open BsmlWrapperN

type generation = Rdm | Imb | Bal

(* Functions to create a random tree *)

let rec aux_insert_random tree v1 v2 continuation =
  match tree with
  | Leaf v -> continuation (Node (v,Leaf v1,Leaf v2))
  | Node (v, l, r) -> 
    let rdm = Random.int 100 in
    if rdm < 50 then 
      aux_insert_random l v1 v2 (fun tl -> continuation (Node(v,tl,r)))
    else  
      aux_insert_random r v1 v2 (fun tr -> continuation (Node(v,l,tr)))

let insert_random tree v1 v2 = 
  aux_insert_random tree v1 v2 (fun x -> x)

let create_random_tree l = 
  let rec aux tree lv = 
    match lv with
    | [] -> tree
    | h1::h2::t -> aux (insert_random tree h1 h2) t
    | _ -> failwith "Not enough value in the list to make an insertion"
  in 
  match l with
  | [] -> failwith "The tree cannot be empty"
  | h :: t -> aux (Leaf h) t

(* Functions to create an imbalanced tree "Comb" *)

let rec create_imbalanced_tree continuation frdm h =
  let rdmV = frdm () in
  let rdmL = frdm () in
  match h with 
  | 0 -> continuation (Leaf rdmV)
  | n -> 
  create_imbalanced_tree (fun tr -> continuation (Node(rdmV , Leaf rdmL, tr))) frdm (n-1)


(* Functions to create a balanced tree *)

let rec create_balanced_tree continuation frdm h =
  let rdm = frdm () in
  match h with 
  | 0 -> continuation (Leaf rdm)
  | n -> 
  create_balanced_tree (fun tl -> create_balanced_tree (fun tr -> continuation (Node(rdm ,tl, tr))) frdm (n-1)) frdm (n-1)

(* Functions to create a tree from a list of values *)

let mk_rdm_list size frdm= 
let rec aux acc n =
    if n == size then acc
    else
      let rdm = frdm () in
      aux (rdm :: acc) (n+1)
  in aux [] 0

let make_odd n =
  if n mod 2 == 0 then n + 1
  else n

let mat_lb n =
  let rec aux acc k =
    let n_acc = (acc * 2) in
    if n_acc > n then k 
    else aux n_acc (k+1)
  in
  if n >= 1 then aux 1 0 else failwith "n must be greater than 0"

let mk_tree g frdm nb =
  match g with
  | Rdm -> 
  let l = mk_rdm_list (make_odd nb) frdm in
  create_random_tree l
  | Imb -> 
  let h = (nb - 1) / 2 in 
  create_imbalanced_tree (fun x -> x) frdm h 
  | Bal -> 
  let h = mat_lb nb in 
  create_balanced_tree (fun x -> x) frdm h 

(* Read of the args *)

let usage () = 
  begin
    print_string ("Usage: "^(Sys.argv.(0))^" filename (true|false) size (rdm|imb|bal) (int min max | float min max | char | bool | matrix size (int min max|float min max| char | bool))\n");
    exit 1;
  end

let verb =
try
  bool_of_string (Sys.argv.(2)) 
with _ -> false

let size_tree =
  try
    int_of_string (Sys.argv.(3))
  with _ -> print_string ("ARG 3 "^Sys.argv.(3)^" incorrect\n"); usage ()

let mode =
  try 
    match lowercase Sys.argv.(4) with
    | "rdm" | "random" -> Rdm
    | "imb" | "imbalanced" -> Imb
    | "bal" | "balanced" -> Bal
    | _ -> failwith "unknown type of tree"
  with _ -> print_string ("ARG 4 "^Sys.argv.(4)^"incorrect\n"); usage ()

let filename = try "../"^ Sys.argv.(1) ^ "_" ^ Sys.argv.(3) ^ ".btree" with _ -> usage ()
let filename_type = try "../"^Sys.argv.(1) ^ "_" ^ Sys.argv.(3) ^ ".type"  with _ -> usage ()
let oc = open_out filename 
let oct = open_out filename_type 

let repeat_c s n=
  let rec aux n acc =
  match n with
  | 0 -> acc
  | n -> aux (n-1) (acc^s)
in aux n ""

let string_of_tree t sta stb=
  let rec aux t h =
    match t with
    | Leaf a -> (repeat_c "\t" h) ^ "Leaf " ^ (sta a) ^ "\n"
    | Node (b,l,r) -> (repeat_c "\t" h) ^ "Node " ^ (stb b) ^ "\n" ^ (aux l (h+1)) ^ "\n" ^ (aux r (h+1))
in aux t 0


let rec buildRdmMatrix n_row n_col rdmf ()= 
  match n_row with
  | 0 -> []
  | n -> 
    let line = mk_rdm_list n_col rdmf in
    line :: (buildRdmMatrix (n-1) n_col rdmf ())

let string_of_row str row =
  let rec aux row acc =
  match row with
  | [] -> acc^"]\n"
  | [h] -> aux [] (acc^(str h))
  | h::t -> aux t (acc^(str h)^"; ")
in aux row "["

let string_of_matrix str mtrx = 
  let rec aux mtrx acc = 
  match mtrx with
  | [] -> acc
  | h :: t -> aux t (acc ^ (string_of_row str h))
in aux mtrx ""

let string_of_nat x = string_of_int (Nint.int_of_n x)

let writeRdmMtrx n_row_col type_mtrx=
  try 
    match type_mtrx with
    | "int" ->
      let min = try int_of_string (Sys.argv.(8)) with _ -> 0 in
      let max = try int_of_string (Sys.argv.(9)) with _ -> 100 in
      let rdmf0 = (fun () -> (Random.int (max - min)) + min) in 
      let rdmf = buildRdmMatrix n_row_col n_row_col rdmf0 in 
      let tree = mk_tree mode rdmf size_tree in
      if verb then print_string (string_of_tree tree (string_of_matrix string_of_int) (string_of_matrix string_of_int)) else ();
      Marshal.to_channel oc tree []; Marshal.to_channel oct ("matrix "^string_of_int(n_row_col)^"*"^string_of_int(n_row_col)^" int") []  

    | "N" ->
      let min = try int_of_string (Sys.argv.(8)) with _ -> 0 in
      let max = try int_of_string (Sys.argv.(9)) with _ -> 100 in
      let rdmf0 = (fun () -> Nint.n_of_int((Random.int (max - min)) + min)) in 
      let rdmf = buildRdmMatrix n_row_col n_row_col rdmf0 in 
      let tree = mk_tree mode rdmf size_tree in
      if verb then print_string (string_of_tree tree (string_of_matrix string_of_nat) (string_of_matrix string_of_nat)) else ();
      Marshal.to_channel oc tree []; Marshal.to_channel oct ("matrix "^string_of_int(n_row_col)^"*"^string_of_int(n_row_col)^" N") []  

    | "float" -> 
      let min = try float_of_string (Sys.argv.(8)) with _ -> 0.0 in
      let max = try float_of_string (Sys.argv.(9)) with _ -> 100.0 in
      let rdmf0 = (fun () -> (Random.float (max -. min)) +. min) in 
      let rdmf = buildRdmMatrix n_row_col n_row_col rdmf0 in 
      let tree = mk_tree mode rdmf size_tree in 
      if verb then print_string (string_of_tree tree (string_of_matrix string_of_float) (string_of_matrix string_of_float)) else ();
      Marshal.to_channel oc tree []; Marshal.to_channel oct ("matrix "^string_of_int(n_row_col)^"*"^string_of_int(n_row_col)^" float") []  

    | "char" -> 
      let rdmf0 = (fun () -> Char.chr (Random.int 255)) in 
      let rdmf = buildRdmMatrix n_row_col n_row_col rdmf0 in 
      let tree = mk_tree mode rdmf size_tree in 
      if verb then print_string (string_of_tree tree (string_of_matrix (String.make 1)) (string_of_matrix (String.make 1))) else ();
      Marshal.to_channel oc tree []; Marshal.to_channel oct ("matrix "^string_of_int(n_row_col)^"*"^string_of_int(n_row_col)^" char") []  

    | "bool" -> 
      let rdmf0 = Random.bool in
      let rdmf = buildRdmMatrix n_row_col n_row_col rdmf0 in 
      let tree = mk_tree mode rdmf size_tree in 
      if verb then print_string (string_of_tree tree (string_of_matrix string_of_bool) (string_of_matrix string_of_bool)) else ();  
      Marshal.to_channel oc tree []; Marshal.to_channel oct ("matrix "^string_of_int(n_row_col)^"*"^string_of_int(n_row_col)^" bool") []

    | _ -> failwith "unknown type of elements"; usage()
  with e -> (print_string (Printexc.to_string e); usage ())  


let _ =
  begin
    try 
      match Sys.argv.(5) with
      | "int" -> 
          let min = try int_of_string (Sys.argv.(6)) with _ -> 0 in
          let max = try int_of_string (Sys.argv.(7)) with _ -> 100 in
          let rdmf = (fun () -> (Random.int (max - min)) + min) in 
          let tree = mk_tree mode rdmf size_tree in
          if verb then print_string (string_of_tree tree string_of_int string_of_int) else (); 
          Marshal.to_channel oc tree []; Marshal.to_channel oct "int" []

      | "N" -> 
          let min = try int_of_string (Sys.argv.(6)) with _ -> 0 in
          let max = try int_of_string (Sys.argv.(7)) with _ -> 100 in
          let rdmf = (fun () -> Nint.n_of_int((Random.int (max - min)) + min)) in 
          let tree = mk_tree mode rdmf size_tree in
          if verb then print_string (string_of_tree tree string_of_nat string_of_nat) else (); 
          Marshal.to_channel oc tree []; Marshal.to_channel oct "N" []

      | "float" -> 
          let min = try float_of_string (Sys.argv.(6)) with _ -> 0.0 in
          let max = try float_of_string (Sys.argv.(7)) with _ -> 100.0 in
          let rdmf = (fun () -> (Random.float (max -. min)) +. min) in 
          let tree = mk_tree mode rdmf size_tree in
          if verb then print_string (string_of_tree tree string_of_float string_of_float) else ();
          Marshal.to_channel oc tree []; Marshal.to_channel oct "float" []

      | "char" -> 
          let rdmf = (fun () -> Char.chr (Random.int 255)) in 
          let tree = mk_tree mode rdmf size_tree in 
          if verb then print_string (string_of_tree tree (String.make 1) (String.make 1)) else (); 
          Marshal.to_channel oc tree []; Marshal.to_channel oct "char" []

      | "bool" -> 
          let rdmf = Random.bool in 
          let tree = mk_tree mode rdmf size_tree in 
          if verb then print_string (string_of_tree tree string_of_bool string_of_bool) else (); 
          Marshal.to_channel oc tree []; Marshal.to_channel oct "bool" []

      | "matrix" -> 
          let n_row_col = try int_of_string(Sys.argv.(6)) with _ -> 1 in
          let type_mtrx = Sys.argv.(7) in
          writeRdmMtrx n_row_col type_mtrx 

      | _ -> failwith "unknown type of elements"

    with e -> (print_string (Printexc.to_string e); usage ());
  close_out oc;
  close_out oct

end


