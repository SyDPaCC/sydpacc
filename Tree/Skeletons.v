Require Import Coq.Lists.List. Import ListNotations.
From SyDPaCC.Bsml Require Import  Model.Core Model.Pid
     DataStructures.DistributedList
     DataStructures.DistributedVector
     Skeletons.StdLib Skeletons.MapReduce.
From SyDPaCC.Core Require Import Bmf Parallelization.
From SyDPaCC.Tree Require Import
     LTree Closure Support.NOption BTree VerticalComposition.
From SyDPaCC.Support Require Import Option UIP.

Generalizable All Variables.

Open Scope N_scope.
Open Scope sydpacc_scope.

  (** * Parallel Binary Trees and their Algorithmic Skeletons *)

Module Make (Import Bsml: Core.BSML).

  Typeclasses eauto := (bfs).
  
  Module Pid       := Pid.Make Bsml.Bsp.
  Module StdLib    := StdLib.Make Bsml Pid.
  Module Import ReplPar   := ReplicatedValue.C Bsml Pid.
  Module Import ParList   := DistributedList.C Bsml Pid.
  Module Import MapReduce := MapReduce.Make Bsml Pid StdLib ParList ReplPar.

  (** ** Parallel Linearized Binary Trees *)

  Definition PLTree A B :=
    { plt: par(list(segment A B)) | valid_tree(ParList.join plt) = true }.

  Program Definition join `(plt: PLTree A B) : LTree A B :=
    ParList.join plt.
  Next Obligation.
    now destruct plt.
  Qed.
  
  #[export] Instance tc_ltree_pltree A B : TypeCorr (@join A B).
  Proof.
    repeat constructor.
    intros [segs Hsegs]; simpl.
    assert(H: exists psegs, ParList.join psegs = segs)
      by apply surjective.
    destruct H as [psegs Hpsegs].
    assert(H: valid_tree(ParList.join psegs) = true)
      by (subst; auto).
    exists(exist _ psegs H).
    unfold join. subst. simpl.
    f_equal.
    apply UIP.Bool.UIP.
  Defined.

  #[export] Instance tc_btree_pltree A B :
    TypeCorr ( (@LTree.join A B) ∘ (@join A B) ).
  Proof. typeclasses eauto. Defined.

  (** ** Algorithmic Skeleetons on Parallel Linearized Binary Trees *)
  
  Section Skeletons.
      
    Definition map_par {A B C D} (kL:A->C) (kN:B->D) :
      par (list (segment A B)) -> par (list (segment C D)) :=
      Eval sydpacc in
      parallel (List.map (map_local kL kN)).
    
    Program Definition map {A B C D} (kL:A->C) (kN:B->D) :
      PLTree A B->PLTree C D :=
      (map_par kL kN) ∘ (@proj1_sig _ _ ).
    Next Obligation.
      autounfold with sydpacc. unfold valid_tree, map_par.
      erewrite @fun_corr with (fp:=MapReduce.par_map (map_local kL kN));
        eauto; try typeclasses eauto.
      destruct x as [ tree Htree ]. simpl proj1_sig.
      set(H:=valid_tree_map).
      specialize (H A B C D kL kN (ParList.join tree) Htree).
      now unfold valid_tree in H.
    Qed.

    #[export] Instance map_ltree_map_par A B C D (kL:A->C) (kN:B->D):
      FunCorr (LTree.map kL kN) (map kL kN).
    Proof.
      constructor. intros [plt Hplt] _.
      unfold map, map_par, join, LTree.map. autounfold with sydpacc; simpl.
      apply ltree_inj; simpl.
      now apply fun_corr.
    Defined.

    #[export] Instance map_tree_map_par `(kL:A->C) `(kN:B->D):
      FunCorr (BTree.map kL kN) (map kL kN).
    Proof.
      typeclasses eauto.
    Defined.
    
    Definition reduce_par {A B C} (k: (A * B * A) -> A)
               `{Hclose: @ClosureU A B C k phi psiN psiL psiR}
               (v:par(list(segment A B))) :
      option A :=
      let local : par (list (sum A C)) :=
          parfun (map_filter_some (reduce_local k phi psiL psiR))
                 v in
      let list : list (sum A C) := ParList.join local in
      reduce_global psiN list. 
    
    Definition reduce {A B C} (k: (A * B * A) -> A) 
               `{Hclose: @ClosureU A B C k phi psiN psiL psiR} :
      PLTree A B -> option A := (reduce_par k) ∘ (@proj1_sig _ _).

    (* Generalization of map correspondence, should be put in MapReduce: *)
    #[export] Instance parfun_corr `(f:list A->list B)
           `{H: Homomorphic _ _ f (@List.app _)} :
      FunCorr f (parfun f).
    Proof.
      constructor. intros ap _.
      unfold ParList.join.
      apply Pid.pids_ind.
      - simpl; autounfold with bsml.
        now autorewrite with bsml list.
      - intros n Hn IH; rewrite Pid.pid_up_to_succ.
        autorewrite with bsml; rewrite IH.
        autounfold with bsml; f_equal; simpl.
        autorewrite with bsml list.
        symmetry. apply homomorphic.
    Defined.

    #[export] Instance homorphic_map_filter_some `(f:A->option B) :
      Homomorphic (map_filter_some f) (@List.app _).
    Proof.
      constructor. intros.
      match goal with
      |[ |- ?x = ?y ] => assert(H: List.map Some x = List.map Some y)
      end.
      repeat( repeat rewrite map_app; repeat rewrite map_filter_some_prop).
      now rewrite filter_app.
      apply Pid.map_inj with (f:=Some); auto.
      intros a a' Heq. now inversion Heq.
    Defined.
      
    #[export] Instance reduce_ltree_reduce_par `(k:A*B*A->A)
             `{Hclose: @ClosureU A B C k phi psiN psiL psiR}:
      FunCorr (LTree.reduce k) (reduce k).
    Proof. 
      repeat constructor. intros [plt Hplt] _.
      unfold reduce, reduce_par, LTree.reduce; autounfold with sydpacc.
      unfold reduce_segs.
      f_equal.
      eapply @fun_corr with (join_A:=@ParList.join (segment A B)); eauto.
      typeclasses eauto.
    Defined.
      
    #[export] Instance reduce_tree_reduce_par `(k:A*B*A->A)
           `{Hclose: @ClosureU A B C k phi psiN psiL psiR} :
      FunCorr (Some ∘ (BTree.reduce k)) (reduce k)(join_B:=(fun x=>x)∘(fun x=>x)).
    Proof. typeclasses eauto. Defined.
    
  End Skeletons.

End Make.

Close Scope sydpacc_scope.
Close Scope N_scope.
