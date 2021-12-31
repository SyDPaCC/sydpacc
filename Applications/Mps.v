Require Import Coq.Lists.List Lia Program SyDPaCC.Core.Bmf. Import ListNotations.
Require Import Structures.Orders Structures.GenericMinMax ZAxioms ZMaxMin.

(* ---------------------------------------------------- *)

(** * MPS: Maximum Prefix Sum *)

(** The MPS application consists of computing the maximum sum of the
    prefixes of a list. In order to make this application generic, we
    parametrized it by a module of numbers. *)

(** ** A Module Type of Numbers *)

(** The considered type of numbers that has an addition, predecessor,
    successor, lower or equal total order, as well as a maximum
    operation that is distributive with respect to addition. The
    addition should form a monoid with its unit and should be
    commutative.  The lower or equal relation should be transitive. *)

Module Type HasMaxAdd := 
  Typ <+ ZeroSuccPred <+ HasEq <+ HasLe <+ HasMax <+ AddSubMul'<+ Opp'.

Module Type MaxProp (Import T : HasMaxAdd).
  #[export] Declare Instance add_max_distr : Distributivity add max.
End MaxProp.

Module Type AddProp (Import T : HasMaxAdd).
  #[export] Declare Instance add_zero_monoid : 
    Monoid add  zero.
  #[export] Declare Instance add_comm : 
    Commutative add.
  Axiom add_opp_diag_l:
    forall n, n + -n = zero.
  #[export] Declare Instance le_trans : Transitive le.
  #[export] Declare Instance le_refl : Reflexive le.
  Axiom add_le : forall n m p, le n m -> le (p + n) (p + m).
End AddProp.

Module Type Number := 
  UsualOrderedTypeFull' <+ HasLeb <+ LebSpec <+ LebIsTotal 
                        <+ ZeroSuccPred' <+ IsNZDomain 
                        <+ OneTwo' <+ IsOneTwo
                        <+ IsNZOrd
                        <+ AddSubMul' <+ IsAddSubMul <+ HasMinMax
                        <+ ZAxiom <+ Opp' <+ IsOpp
                        <+ MaxProp <+ AddProp.

(** ** Derivation of an Efficient MPS Application *)

(** The following module is a systematic development of an efficient
    sequential function for the MPS problem. *)

Module Make(Import N : Number).

  Module Import A := UsualMinMaxProperties N N.

  #[export] Instance max_assoc : Associative max.
  Proof. 
    constructor; intros; rewrite max_assoc; trivial.
  Qed.

  (** *** Specification of the MPS problem *)
  
  (** Sum of a number list *)
  Program Definition sum : list t -> t := reduce add.

  (** Maximum of a non-empty number list *)
  Definition maximum : forall (l:list t), NonEmpty l -> t :=
    NE.reduce max.
  
  Program Definition mps_spec : list t -> t :=  
    maximum ∘' (map sum) ∘'' prefix.

  (** The MPS specification cannot be expressed as a rightwards
      function.  It is necessary to tuple it with the function [sum]
      to be able to do so. *)
  Definition ms_spec := tupling mps_spec sum.

  (** *** Some properties of [sum] and [max] *)
  Fact map_sum : forall (l:list(list t))(a:t), 
                   map sum (map (cons a) l) = map (add a) (map sum l).
  Proof.
    induction l as [ | y ys IH]; intro a; simpl.
    - trivial.
    - unfold sum, reduce; simpl; f_equal.
      + rewrite <- fold_left_prop by typeclasses eauto; f_equal.
        now rewrite left_neutral, right_neutral by typeclasses eauto.
      + repeat rewrite map_map.
        apply map_ext; intros; simpl.
        rewrite <- fold_left_prop by typeclasses eauto.
        now rewrite (left_neutral a), (right_neutral a).
  Qed.
   
  Fact maximum_add : forall (l:list t)(a b:t) {HNE:NonEmpty l},
                       fold_left max (map (add a) l) b = max b (a + NE.reduce max l).
  Proof.
    induction l as [ |y ys IH]; simpl; intros a b HNE.
    - inversion HNE; intuition.
    - case ys as [|y' ys']. 
      + trivial.
      + rewrite fold_left_prop by typeclasses eauto.
        rewrite (IH _ _ (cons_non_empty _ _)).
        rewrite <- left_distributivity.
        repeat f_equal. unfold NE.reduce; simpl.
        now rewrite <- fold_left_prop by typeclasses eauto.
  Qed.

  (** *** [ms_spec] is a opl-leftwards *)
  Definition opl (a:t) (b:t*t) : t*t := 
    ( max 0 (a + fst b), a + (snd b) ).
  
  #[export] Instance ms_leftwards : Leftwards ms_spec opl (0,0).
  Proof.
    constructor; induction l as [ | x xs IH ]; simpl.
    - trivial.
    - rewrite <- IH; clear IH.
      unfold ms_spec, tupling, ms_spec, mps_spec, sum, compose, comp', comp'', 
      reduce, opl; simpl. 
      assert(forall a, fold_left max (map sum (map (cons a) (prefix xs))) 0 =
             max 0 (a + NE.reduce max (map sum (prefix xs)))) as H1.
      {
        induction xs as [ | y ys IH]; intro a.
        - unfold sum, reduce; simpl. 
          now rewrite (left_neutral a), (right_neutral a).
        - now rewrite map_sum, (maximum_add (map sum(prefix(y::ys))) _ _ ).
      }
      assert(x + fold_left add xs 0 = fold_left add xs (0 + x)) as H2
          by now rewrite <- fold_left_prop, (left_neutral x), (right_neutral x)
            by typeclasses eauto.
      unfold sum, reduce in *; now rewrite H1, H2.
  Qed.

  (** *** [ms_spec] is a opr-rightwards *)
  Definition opr (a:t*t) (b:t) : t*t := 
    (max (fst a) ((snd a)+b),(snd a)+b).

  #[export] Instance ms_rightwards : Rightwards ms_spec opr (0,0).
  Proof.
    constructor; induction l as [ | x xs IH ] using rev_ind; simpl.
    - trivial.
    - unfold ms_spec, tupling, ms_spec, mps_spec, compose, comp', comp'' in *.
      rewrite fold_left_app. 
      replace(NE.reduce max (map sum (prefix (xs++[x])))) 
      with (max(NE.reduce max (map sum (prefix xs))) 
               (NE.reduce max (map sum [xs++[x]])))
        by (rewrite <- NE.reduce_app; apply NE.reduce_pi with (op:=max);
            rewrite prefix_app, map_app; trivial).
      simpl.
      replace (sum(xs++[x])) with (sum xs + x)
        by (unfold sum, reduce; simpl; rewrite fold_left_app; trivial).
      rewrite surjective_pairing in IH.
      inversion IH. 
      pattern (NE.reduce max (map sum (prefix xs))); rewrite  H0.
      pattern(sum xs); rewrite H1.
      unfold opr; simpl; reflexivity.
  Qed.

  (** *** [ms'] is a weak right inverse droit of [ms_spec] *)
  Definition ms' (p:t*t) := let (m,s) := p in [ m; s + -m].

  #[export] Hint Unfold ms_spec ms_spec ms' tupling sum reduce mps_spec compose comp' comp'' : ms.

  Lemma sum_cons :
    forall a l, sum (a::l) = a + sum l.
  Proof.
    intros a l.
    unfold sum, reduce. simpl.
    replace (0 + a) with (a + 0) by
      (now rewrite right_neutral, left_neutral by typeclasses eauto).
    now rewrite fold_left_prop by typeclasses eauto.
  Qed.

  Lemma mps_cons :
    forall h t, mps_spec (h::t) = max 0 (h + mps_spec t).
  Proof.
    intros h t.
    unfold mps_spec, comp', comp''.
    simpl. rewrite map_sum.
    replace (sum []) with 0 by now compute.
    now erewrite maximum_add.
  Qed.
  
  Lemma sum_le_mps_spec: forall l, sum l <= mps_spec l.
  Proof.
    induction l as [ | h t IH].
    - compute. apply reflexivity.
    - rewrite mps_cons, sum_cons.
      apply transitivity with (y := max 0 (h + sum t)).
      + apply le_max_r.
      + apply max_le_compat_l.
        now apply add_le.
  Qed.

  Corollary max_sum_mps :
    forall l, max (mps_spec l) (sum l) = mps_spec l.
  Proof. intro l. apply max_l, sum_le_mps_spec. Qed. 

  Lemma le_0_mps : forall l, 0 <= mps_spec l.
  Proof.
    induction l as [ | h t IH].
    - now compute.
    - rewrite mps_cons.
      apply le_max_l.
  Qed.
  
  #[export] Program Instance ms_right_inverse : Right_inverse ms_spec ms'.
  Next Obligation.
    assert(H1: mps_spec l = mps_spec [mps_spec l; sum l + - mps_spec l]).
    {
      assert(forall a b, sum[a;b + -a] = b) as H.
      {
        autounfold with ms; compute; intros.
        now rewrite (left_neutral a), (commutative b),
        <- associative, add_opp_diag_l, left_neutral.
      }
      assert(forall a, sum [a] = a) as Hs
          by (autounfold with ms ; simpl; apply left_neutral).
      pose (Hmax:=max_sum_mps).
      unfold mps_spec, comp', comp'' in *. simpl.
      rewrite H, Hs, associative, Hmax.
      now rewrite max_r by apply le_0_mps.
    }
    assert(H2: sum l = sum [mps_spec l; sum l + - mps_spec l]).
    {
      unfold sum, reduce. simpl.
      rewrite (@commutative _ add) by typeclasses eauto.
      rewrite add_0_l.
      rewrite (@associative _ add) by typeclasses eauto.
      replace ((- mps_spec l + mps_spec l)) with (mps_spec l + - mps_spec l)
        by apply commutative.
      rewrite add_opp_diag_l.
      now rewrite right_neutral.
    }
    unfold ms_spec. autounfold with sydpacc.
    now f_equal.
  Qed.

  (** *** [ms_spec] is an homomorphism *)
  #[export] Instance ms: Homomorphic ms_spec (fun l r=>ms_spec(ms' l ++ ms' r)).
    typeclasses eauto.
  Qed.
  
  (** *** Optimization of this Homomophism *)

  (** Some properties of [sum] and [mps_spec] *)
  Lemma mps_sum : 
    forall l, sum l <= mps_spec l.
  Proof.
    intro l. unfold mps_spec, compose, comp', comp'', maximum.
    destruct l as [ | x1 xs ].
    - apply le_lteq; now right.
    - simpl prefix; simpl map.
      rewrite (NE.reduce_fold_left max (sum []) (map sum (map (cons x1) (prefix xs)))).
      rewrite <-(max_id (sum [])).
      replace (fold_left max (map sum (map (cons x1) (prefix xs)))
                         (max (sum []) (sum [])))
      with (fold_left max (map sum (prefix (x1::xs))) (sum [])) by auto.
      rewrite (prefix_last (l:=(x1::xs))) by typeclasses eauto.
      rewrite map_app, fold_left_app; simpl.
      apply le_max_r.
  Qed.

  Lemma mps_prop : 
    forall l, 0 <= mps_spec l.
  Proof.
    induction l.
    - repeat autounfold; simpl; apply le_lteq; now right.
    - set(H:=leftwards (a::l)).
      unfold ms_spec,tupling in H.
      rewrite surjective_pairing in H.
      inversion H. rewrite H1.
      apply le_max_l.
  Qed.

  Lemma img_ms_spec_prop `(a: img ms_spec) : 
    snd (proj1_sig a) <= fst (proj1_sig a) /\ 0 <= fst (proj1_sig a).
  Proof.
    destruct a as [a [l H]]; simpl.
    unfold ms_spec, tupling in H; destruct a; inversion H; subst; simpl.
    split; [apply mps_sum | apply mps_prop ].
  Qed.

  Fact sum_add_opp: 
    forall a b l, sum (a::(b + -a)::l) = b + sum l.
  Proof.
    autounfold with ms; compute; intros a' b' l;
    rewrite (left_neutral a'), (commutative b'),
    <- associative, add_opp_diag_l.
    now rewrite <- fold_left_prop, (commutative b') by typeclasses eauto.
  Qed.
  
  (** An optimised version of the binary operator defining the homomophism *)
  #[export] Program Instance opt_op : Optimised_op ms_spec.
  Next Obligation.
    assert(forall m n, m + (n + - m) = n)
      as add_opp by 
          (intros; rewrite <- associative, commutative, <- associative, 
                   commutative with (y:=m);
           rewrite add_opp_diag_l, left_neutral; reflexivity).
    eexists. 
    intros a b.
    pose(H1:= img_ms_spec_prop a). destruct H1 as [H1 H1'].
    pose(H2:= img_ms_spec_prop b). destruct H2 as [H2 H2'].    
    unfold restrict; simpl.
    rewrite surjective_pairing with (p:=proj1_sig a). 
    rewrite surjective_pairing with (p:=proj1_sig b). 
    unfold ms', ms_spec, mps_spec, tupling, comp', comp''; subst.
    simpl in *.
    repeat rewrite sum_add_opp.
    replace (sum []) with 0 by auto.
    repeat rewrite @right_neutral with (op:=add)(e:=0)
      by typeclasses eauto.
    assert(forall x, sum [x] = x) 
      as Hs by (intros; repeat autounfold with ms; simpl; apply left_neutral).
    repeat rewrite Hs.
    rewrite max_r with (y:=fst (proj1_sig a)) by assumption.
    rewrite max_l with (x:=fst (` a)) by assumption.
    rewrite associative, <- left_distributivity.
    rewrite max_l with (x:=fst (` b)) by assumption.
    reflexivity.
  Defined.

  #[export] Program Instance opt_f : Optimised_f ms_spec.
  Next Obligation.
    eexists. intro a. compute. rewrite (left_neutral a).
    reflexivity.
  Defined.
    
End Make.
