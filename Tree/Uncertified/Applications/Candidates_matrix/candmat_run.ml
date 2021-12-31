open BsmlWrapperN
open BTree
open LTree
open Candidates

module App = Make(Bsml)
open App

(* ARGUMENTS MANAGEMENT *)
let usage () = 
  begin
    print_string ("Usage: "^(Sys.argv.(0))^" (seq|par) filename [yes|no] \n");
    exit 1;
  end

let mode =
  try 
    match Sys.argv.(1) with
    | "par" -> true
    | _ -> false
  with _ -> print_string ("[ERROR] Unknown "^Sys.argv.(1)^". \n"); usage ()

let filename =  Sys.argv.(2)
let filename_bt = "../"^filename ^ ".btree" 
let filename_lt = "../"^filename ^"_"^(string_of_int Bsmlmpi.bsp_p) ^ ".ltree"

let verb =
  try
    match Sys.argv.(4) with
    | "yes" -> true
    | _ -> false
  with _ -> false


(* MAIN FUNCTIONS *)
let option_to_string ts o =
  match o with
  | None -> "_"
  | Some a -> ts a

let from_to n1 n2 =
  let rec aux n2 list =
    if n1>n2
    then list
    else aux (n2-1) (n2::list) in
  aux n2 []

let procs = from_to 0 (Bsmlmpi.bsp_p-1)
          
let to_list (v:'a Bsml.par) : 'a list =
  let f = Bsmlmpi.proj v in
  List.map f procs

let at_root f =
  ignore(Bsmlmpi.mkpar(fun i-> if i=0 then f () else ()))

let cost output to_string =
  let p = Bsmlmpi.bsp_p in
  let r = to_string output in
  let costs = to_list (Bsmlmpi.get_cost()) in
  let max_cost = List.fold_left max 0.0 costs in
  at_root(fun _ ->
    (if verb
     then
       begin
         Printf.printf "[ ";
         List.iter (Printf.printf"%f ") costs;
         Printf.printf "]\n"
       end);
    Printf.printf "%d\t %f\t %s\n" p max_cost r);
  output

let run f input ts =
  let _ = Bsmlmpi.start_timing() in
  let _ = Gc.full_major() in 
  let _ = Bsmlmpi.stop_timing () in  
  let _ = Bsmlmpi.start_timing() in
  let output = f input in
  let _ = Bsmlmpi.stop_timing () in  
  cost output ts

let print_dg () =
  at_root(fun () ->
      if verb
      then
        begin
          Printf.printf("Data are imported.\n");
          flush stdout;
        end)




let rec transpose l = 
  match l with
  | [] -> []
  | [] :: xss  -> transpose xss
  | (x::xs) :: xss -> (x :: List.map List.hd xss) :: transpose (xs :: List.map List.tl xss);;

let matrix_multiply m1 m2 =
  let rec aux f m =
    if List.mem [] m then []
      else f (List.map List.hd m) :: aux f (List.map List.tl m)
    in
  List.map (fun row -> aux (fun col -> List.fold_left (+.) 0. (List.map2 ( *. ) row col)) m2) m1;;

let is_identity m =
  let len = List.length m in 
  let rec aux m n =
    if n >= len then true 
  else 
      
      let row = 
        try
          (List.nth m (n))
        with
        | _ -> failwith ( "tried to access to row "^(string_of_int n) )
      in
      let sum = List.fold_left (fun acc x -> acc + x) 0 row in
      if List.nth row n == 1 && sum == 1 
      then aux m (n+1)
      else false
  in aux (List.map (List.map truncate) m) 0;;

(* MAIN *)
let _ = 
  let is_orthogonal m = 
    let mt = transpose m in 
    is_identity (matrix_multiply m mt) 
  in
  let string_of_nat x = string_of_int (Nint.int_of_n x) in
  
  if mode then

    if Sys.file_exists filename_lt then
      let input = Bsmlmpi.mkpar 
        (fun i -> 
          let file_i = filename_lt ^ "."^(string_of_int i) in
          (
            (* print_string (" I am the proc" ^ (string_of_int i) ^" and I am looking for the file "^ file_i^ "\n"); *)
          if Sys.file_exists file_i then 
            let res = Marshal.from_channel (open_in file_i) in
            res
          else [])
        ) in 
        begin
          print_dg();
          let f = candidates is_orthogonal is_orthogonal in
          run f input (option_to_string string_of_nat)
        end
    else
      failwith ("The dataset " ^ filename_lt ^ " doesn t exist")

  else
    if Sys.file_exists filename_bt then
      let input =  Marshal.from_channel (open_in filename_bt) in
      begin
        print_dg();
        let f = spec_candidates is_orthogonal is_orthogonal in
        run f input (option_to_string string_of_nat)
      end
    else
      failwith ("The dataset " ^ filename_bt ^ " doesn t exist")