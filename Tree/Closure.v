Set Implicit Arguments.

(* TODO: one field per property *)
(* TODO: remain ClosureU into Closure *)
Class ClosureU {A B C}
      (k : A * B * A -> A) (phi : B -> C) (psiN : A * C * A -> A)
      (psiL : C * C * A -> C) (psiR: A * C * C -> C) :=
  {
    closed_u : (forall l b r, k (l,b,r) = psiN (l, phi b, r))
               /\ (forall x l y b r, psiN(psiN (x,l,y),b,r) = psiN(x,psiL(l,b,r),y))
               /\ (forall x l y b r, psiN(l,b,psiN(x,r,y)) = psiN (x,psiR(l,b,r),y))
    
  }.
