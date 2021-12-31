Require Import Coq.Lists.List NArith Lia Bool.
Import ListNotations.
From SyDPaCC.Tree    Require Import BTree LTree.
From SyDPaCC.Support Require Import Option List UIP.

Set Implicit Arguments.
Generalizable All Variables.

Open Scope N_scope.

Section Tools.

  Fixpoint from_to_aux (start count: nat) (acc:list nat) : list nat :=
    match count with
    | 0 => acc
    | S count' => from_to_aux start count' ((start+count')::acc)
    end%nat.
  
  Definition from_to (n1 n2: N) : list N :=
    List.map N.of_nat (from_to_aux (N.to_nat n1) (N.to_nat (n1+n2-1)) []).
  
  Fixpoint nodes_aux (label:N) (trees: list(t N N)) acc : list (t N N) * N :=
    match trees with
    | [ ] => (acc, label)
    | [tree] => (tree::acc, label)
    | tree1::tree2::trees =>
      nodes_aux (label+1) trees ((Node label tree1 tree2)::acc)
    end.
  
  Definition nodes (trees_label: list(t N N) * N) : list (t N N) * N :=
    let (trees, label) := trees_label in 
    let res := nodes_aux label trees [] in
    ( List.rev'(fst res), snd res ).
  
  Fixpoint iter A count (f:A->A) init :=
    match count with
    | 0%nat => init
    | S count => iter count f (f init)
    end.
  
  Definition make init :=
    let trees := iter 100 nodes init in
    List.hd (Leaf 0)(fst trees).
  
  Definition generate (num: N) :=
    let leaves := List.map (@Leaf N N) (from_to 1 num) in
    make (leaves, num+1).

End Tools.
  
Section Examples.

  Definition btree1 := Eval cbv in generate 100. Print btree1.

  Definition btree2 := Eval cbv in generate 37.  Print btree2. 

  Definition btree3 := Eval cbv in generate 64.  Print btree3.

  Definition btree4 :=
    Node 1
         (Node 2
               (Node 4
                     (Leaf 6)
                     (Leaf 7))
               (Node 5
                     (Leaf 8)
                     (Leaf 9)))
         (Leaf 3).
  
  Definition btree5 :=
    Node 13
         (Node 3
               (Leaf 1)
               (Leaf 1))
         (Node 9
               (Node 7
                     (Node 3
                           (Leaf 1)
                           (Leaf 1))
                     (Node 3
                           (Leaf 1)
                           (Leaf 1)))
               (Leaf 1)).

  Definition btree6 := Eval cbv in
        make ([btree1; btree4; btree2; btree5; btree3 ], 200).

  Definition btree7 := Eval cbv in
        make ([btree4; btree5; btree4; btree5; btree4 ], 50).

  Definition btree8 := (Node 10 ((Node 20 ((Node 16 (Leaf 13) ((Node 0 ((Node 15 ((Node 10 ((Node 17 ((Node 8 ((Node 1 (Leaf 18) (Leaf 3) )) ((Node 14 (Leaf 20) (Leaf 4) )) )) ((Node 11 (Leaf 13) ((Node 1 (Leaf 9) (Leaf 20) )) )) )) ((Node 2 ((Node 17 (Leaf 0) ((Node 1 (Leaf 7) (Leaf 20) )) )) ((Node 7 (Leaf 18) ((Node 11 (Leaf 11) (Leaf 7) )) )) )) )) ((Node 5 ((Node 4 ((Node 11 ((Node 2 (Leaf 19) (Leaf 6) )) ((Node 6 (Leaf 12) (Leaf 5) )) )) ((Node 0 (Leaf 7) ((Node 5 (Leaf 15) (Leaf 6) )) )) )) ((Node 1 (Leaf 19) ((Node 11 ((Node 8 (Leaf 20) (Leaf 12) )) (Leaf 8) )) )) )) )) (Leaf 5) )) )) ((Node 2 ((Node 17 ((Node 16 (Leaf 17) (Leaf 19) )) ((Node 16 ((Node 13 (Leaf 1) (Leaf 13) )) ((Node 11 ((Node 3 ((Node 15 (Leaf 8) ((Node 11 (Leaf 9) (Leaf 20) )) )) (Leaf 15) )) (Leaf 6) )) )) )) (Leaf 7) )) )) ((Node 15 ((Node 8 ((Node 6 ((Node 19 ((Node 12 ((Node 20 ((Node 6 ((Node 12 (Leaf 10) (Leaf 4) )) ((Node 12 (Leaf 16) (Leaf 9) )) )) ((Node 9 (Leaf 11) (Leaf 0) )) )) ((Node 20 ((Node 9 (Leaf 4) ((Node 10 (Leaf 0) (Leaf 9) )) )) ((Node 19 (Leaf 20) ((Node 19 (Leaf 0) (Leaf 11) )) )) )) )) ((Node 15 ((Node 13 ((Node 16 ((Node 1 (Leaf 3) (Leaf 11) )) (Leaf 5) )) ((Node 11 (Leaf 20) ((Node 0 (Leaf 7) (Leaf 15) )) )) )) (Leaf 17) )) )) ((Node 15 ((Node 6 (Leaf 11) ((Node 10 (Leaf 2) (Leaf 14) )) )) ((Node 4 ((Node 4 (Leaf 16) ((Node 6 (Leaf 11) ((Node 10 (Leaf 3) (Leaf 11) )) )) )) ((Node 3 ((Node 6 ((Node 18 (Leaf 8) (Leaf 12) )) ((Node 3 (Leaf 16) (Leaf 8) )) )) ((Node 6 ((Node 15 (Leaf 6) (Leaf 5) )) (Leaf 5) )) )) )) )) )) (Leaf 0) )) ((Node 10 ((Node 18 ((Node 3 ((Node 1 ((Node 16 ((Node 20 ((Node 6 (Leaf 19) (Leaf 10) )) (Leaf 3) )) ((Node 17 ((Node 13 (Leaf 16) (Leaf 4) )) ((Node 4 (Leaf 17) (Leaf 9) )) )) )) (Leaf 5) )) ((Node 8 ((Node 4 ((Node 0 ((Node 1 (Leaf 10) (Leaf 8) )) (Leaf 5) )) ((Node 18 (Leaf 15) (Leaf 4) )) )) ((Node 18 ((Node 4 (Leaf 7) ((Node 4 (Leaf 16) (Leaf 19) )) )) ((Node 10 (Leaf 13) ((Node 18 (Leaf 4) (Leaf 8) )) )) )) )) )) ((Node 10 ((Node 14 ((Node 19 ((Node 18 (Leaf 9) (Leaf 20) )) (Leaf 20) )) ((Node 0 (Leaf 4) (Leaf 0) )) )) (Leaf 9) )) )) ((Node 6 ((Node 5 ((Node 7 ((Node 11 ((Node 0 ((Node 11 (Leaf 14) (Leaf 5) )) ((Node 12 (Leaf 19) (Leaf 16) )) )) ((Node 2 (Leaf 10) (Leaf 15) )) )) (Leaf 20) )) (Leaf 16) )) (Leaf 10) )) )) )) ).

  Definition ltree16  := Eval cbv in serialization btree1 6.  Print ltree16.
  Definition ltree117 := Eval cbv in serialization btree1 17. Print ltree117.
  Definition ltree29  := Eval cbv in serialization btree2 9.  Print ltree29.
  Definition ltree211 := Eval cbv in serialization btree2 11. Print ltree211.
  Definition ltree33  := Eval cbv in serialization btree3 3.  Print ltree33.
  Definition ltree37  := Eval cbv in serialization btree3 7.  Print ltree37.

  Definition ltree44  := Eval cbv in serialization btree4 4. Print ltree44.
  Definition ltree43  := Eval cbv in serialization btree4 3. Print ltree43.
  Definition ltree42  := Eval cbv in serialization btree4 2. Print ltree42.
  Definition ltree41  := Eval cbv in serialization btree4 1. Print ltree41.

  Definition ltree55  := Eval cbv in serialization btree5 5. Print ltree55.
  Definition ltree54  := Eval cbv in serialization btree5 4. Print ltree54.
  Definition ltree53  := Eval cbv in serialization btree5 3. Print ltree53.
  Definition ltree52  := Eval cbv in serialization btree5 2. Print ltree52.

  Definition ltree63  := Eval cbv in serialization btree6 3.  Print ltree63.
  Definition ltree666 := Eval cbv in serialization btree6 66. Print ltree666.

  Definition ltree71  := Eval cbv in serialization btree7 1.  Print ltree71. 
  Definition ltree757 := Eval cbv in serialization btree7 57. Print ltree757.

  Eval cbv in segments_to_subtrees ltree53.
  
  Eval compute in
      ( deserialization ltree53,  ltree53, btree5).

  Definition add3 (p: N * N * N) : N :=
    (fst(fst p)) + (snd(fst p)) + (snd p).

  Definition reduction :=
    fun lt => reduce_global add3 (map_filter_some (reduce_local add3 (fun x=>x) add3 add3) lt).

  Compute reduction (serialization btree8 1).
  Compute reduction (serialization btree8 11).
  Compute reduction (serialization btree8 37).
  Compute reduction (serialization btree8 10).

  Compute
      List.map
        reduction
        [ ltree16; ltree117; ltree29; ltree211; ltree33; ltree37;
            ltree44; ltree43; ltree42; ltree41; ltree55; ltree54; ltree53; ltree52;
              ltree63; ltree666; ltree71; ltree757; (serialization (generate 10000) 111) ].

End Examples.

Close Scope N_scope.
