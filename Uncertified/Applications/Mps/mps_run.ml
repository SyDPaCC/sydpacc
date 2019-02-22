open BsmlWrapperN

let from_to n1 n2 =
  let rec aux n2 list =
    if n1>n2
    then list
    else aux (n2-1) (n2::list) in
  aux n2 []

let create size =
  let rec aux size list =
    if size = 0
    then list
    else aux (size-1) (((Random.int size)-(size/2))::list) in
  aux size []

module App = BsmlMps.Make (Bsml) (Numint)

let to_list (v:'a Bsml.par) : 'a list =
  let f  = Bsmlmpi.proj v in
  List.map f (from_to 0 (Bsmlmpi.bsp_p-1))

let size =
  try
    int_of_string (Sys.argv.(1))
  with _ ->
    begin
      print_string ("Usage: "^(Sys.argv.(0))^" global_size (multiple of bsp_p)\n");
      exit 1;
    end

let _ =
  Random.self_init ();
  let input = Bsml.mkpar(fun i->create (size/Bsmlmpi.bsp_p)) in
  let _ = Bsmlmpi.start_timing() in
  let output = App.par_mps input in
  let _ = Bsmlmpi.stop_timing () in
  let cost = (fun (h::t)->List.fold_left max h t) (to_list (Bsmlmpi.get_cost())) in 
  Bsmlmpi.mkpar(function
      | 0 ->
        begin
	  print_int (Bsmlmpi.bsp_p);
          print_string "\t";
	  print_float cost;
          print_string "\t";
          print_int output;
          print_newline ();
          flush stdout
        end
      | _ -> ())

