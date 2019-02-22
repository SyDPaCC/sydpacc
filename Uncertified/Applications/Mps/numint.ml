open Datatypes

type t = int

let eq_dec x y = x = y

let leb x y = x <= y
  
let zero = 0
  
let succ x = x+1
  
let pred x = x-1

let one = 1

let two = 2

let add = ( + )

let sub = ( - )

let mul = ( * )

let max x y = if x<y then y else x

let min x y = if x<y then x else y

let opp x = -x

let compare x y =
  if x = y
  then Eq
  else if x < y then Lt else Gt



