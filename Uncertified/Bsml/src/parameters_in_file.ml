open String

type bsp = { p : int ; g : float ; l : float; r : float }

let parameters = ref {p=16;g=18.;l=72000.;r=5000.}

let list_from_string s separator  = 
  let rec aux (s,l) = 
    if not(contains s separator)
    then ("",s::l)
    else
      let i = index s separator in
      let new_s = sub s (i+1) (length s - 1 -i) 
      and element = sub s 0 i in
	aux (new_s,element::l) in
    List.rev(snd(aux (s,[])))

let error = 
  "The BSP parameters file should have the form: "^
  "int,float,float,float (p,g,l,r)"
  
let read p =
  let processline s =
    match list_from_string s ',' with
    | ps::l ->
      begin
        match List.map float_of_string l with
        | [g;l;r] -> {p=(int_of_string ps); g=g; l=l; r=r;}
        | _ -> failwith error
      end
    | [] -> failwith error in
  let chin = 
    try 
      open_in ((Sys.getenv "HOME")^"/.bsmlrc") 
    with _ -> 
      (print_string "~/.bsmlrc unavailable.\n";flush stdout; exit 1) in
  let theparameters = ref(processline (input_line chin)) in
    try
      if p=0 
      then parameters := !theparameters
      else
	begin
	  while !theparameters.p<>p do
	    theparameters:=processline (input_line chin)
	  done;
	  parameters:=!theparameters;
	end
    with _ -> 
      begin
	(if (!theparameters.p<>p)
	 then parameters:={p=p;g=0.;l=0.;r=0.}
	 else parameters:=!theparameters);
	close_in chin
      end
      
let get () = !parameters
