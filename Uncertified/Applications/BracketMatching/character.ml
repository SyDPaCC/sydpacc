type t = char

let is_open c =
      c = '(' || c = '[' || c = '{'

let is_close c =
      c = ')' || c = ']' || c = '}'

let are_matched c c' =
  match c,c' with
  | '(',')' | '[',']' | '{','}' -> true
  | _ -> false

let matches =
  function
  | '(' -> ')'
  | '[' -> ']'
  | '{' -> '}'
  | c -> c
