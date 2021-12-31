open BsmlWrapperN

let from_to n1 n2 =
  let rec aux n2 list =
    if n1>n2
    then list
    else aux (n2-1) (n2::list) in
  aux n2 []

let procs = from_to 0 (Bsmlmpi.bsp_p-1)

let replicate x = Bsmlmpi.mkpar(fun _ -> x)

let parfun f v = Bsmlmpi.apply(replicate f) v
      
module Par = BsmlBm.Make (Bsml) (Character)

let to_list (v:'a Bsml.par) : 'a list =
  let f  = Bsmlmpi.proj v in
  List.map f procs

let usage () = 
  begin
    print_string ("Usage: "^(Sys.argv.(0))^" (seq|par) global_size [yes|no] \n");
    exit 1;
  end

let mode =
  try 
    match Sys.argv.(1) with
    | "par" -> true
    | _ -> false
  with _ -> usage ()
         
let size =
  try
    int_of_string (Sys.argv.(2))
  with _ -> usage ()

let verb =
  try
    match Sys.argv.(3) with
    | "yes" -> true
    | _ -> false
  with _ -> false

let bool_of_string b =
  if b then "true" else "false"

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

let rec take_aux n xs acc =
  if n <= 0
  then List.rev acc
  else match xs with 
       | [] -> []
       | x::xs -> take_aux (n-1) xs (x::acc)

let take n xs = take_aux n xs []

let rec drop n xs =
  if n<=0
  then xs
  else drop (n-1) (List.tl xs)

			   
let set_states () =
  let sent =
    Bsmlmpi.put(Bsmlmpi.mkpar(fun src->
		if src=0
		then let state = (Random.self_init();Random.get_state ()) in
		     fun dst -> [state]
		else fun dst -> [])) in
  let states = parfun (fun msgs->List.hd (msgs 0)) sent in
  ignore(parfun Random.set_state states)
	
let mk_data size =
  begin
    let rem = size mod Bsmlmpi.bsp_p in
    let lsz = size/Bsmlmpi.bsp_p in
    let drops pid = pid * lsz + if pid < rem then pid else rem in
    let takes pid = lsz + if pid < rem then 1 else 0 in
    at_root(fun _ ->if verb then Printf.printf "Generating data ...\n"; flush stdout);
    let raw_input = Generator.create_wf 10 size in
    let input = Bsmlmpi.mkpar(fun i->take (takes i)(drop (drops i) raw_input)) in
    begin
      (if verb then
	 let sizes = to_list (parfun List.length input) in
	 at_root(fun()->List.iteri (Printf.printf "  size[%d] = %d\n") sizes));
      Gc.full_major();
      at_root(fun _->if verb then Printf.printf "... data generated.\n"; flush stdout);
      input
    end
  end

let run f input ts =
  let _ = Bsmlmpi.start_timing() in
  let output = f input in
  let _ = Bsmlmpi.stop_timing () in  
  cost output ts

let _ =
  if mode
  then
    let input = mk_data size in
    let f = Par.par_bm [] in
    run f input bool_of_string
  else
    let input = Generator.create_wf 10 size in
    let f =  Par.bm_spec []  in
    run f input bool_of_string
