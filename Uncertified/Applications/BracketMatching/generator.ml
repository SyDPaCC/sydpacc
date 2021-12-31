open Character

let rec create_wf_aux depth size stack acc =
  let lowercase () = char_of_int(97+Random.int 26) in
  if size <= List.length stack 
  then List.rev ((List.rev(List.map matches stack))@acc)
  else
    let rnd_c = char_of_int(32+Random.int 94) in
    let c = 
      if (is_open rnd_c) && (List.length stack = depth)
      then lowercase ()
      else if (is_close rnd_c) && 
		(stack = [] || not(are_matched (List.hd stack) rnd_c))
      then lowercase ()
      else rnd_c in
    let new_stack =
      if is_open c then c::stack
      else if is_close c then List.tl stack
      else stack in
    create_wf_aux depth (size-1) new_stack (c::acc)

(** [create depth size ] creates as well parenthesised list of
    characters, with at most a [depth] of nested parenthesis, and the
    generated list has length [size]. *)
let create_wf depth size =
  create_wf_aux depth size [] []
