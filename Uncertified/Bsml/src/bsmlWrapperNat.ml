open Bsmlmpi
open Natint
open Core

module Bsml : BSML with type 'a par = 'a Bsmlmpi.par  =
struct

  (** Parallel vector are those of BSML  *)
  type 'a par = 'a Bsmlmpi.par

  (** [bsp_p] is the Peano encoding of the number of processors  *)
  module Bsp =
  struct
    let p = nat_of_int (Bsmlmpi.bsp_p)
  end

  (** get is for specification purpose only, it should not appear in programs *)
  let get v i = failwith "get is for specification purpose only"

  (** creator of parallel vector *)
  let mkpar f = Bsmlmpi.mkpar (fun i -> f (nat_of_int i))

  (** apply is the point-wise  application of vectors *)
  let apply = Bsmlmpi.apply

  let parfun f v = apply (Bsmlmpi.mkpar(fun _->f)) v
  
  (** Communication primitive *)
  let put vf =
    parfun (fun f n ->f(int_of_nat n)) 
      (Bsmlmpi.put(parfun (fun f i->f(nat_of_int i)) vf))

  let proj v = fun n -> (Bsmlmpi.proj v) (int_of_nat n)

end
