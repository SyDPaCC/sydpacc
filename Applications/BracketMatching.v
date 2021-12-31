Require Import Coq.Lists.List NArith Lia. Import ListNotations.
From SyDPaCC.Core Require Import Bmf Diffusion.
Require Import SyDPaCC.Support.NList.
Set Implicit Arguments.
Generalizable All Variables.

Open Scope N_scope.

(* ---------------------------------------------------- *)

(** * BM: Bracket Matching *)

(** The bracket matching algorithm determines whether the brackets
    (possibly of several kind) in a given string are correctly
    matched.  For example it is the case in [(3-2)*3]*{8} but not in
    {2+1]. *)

(** ** A Module Type for Characters *)

(** We consider that strings are lists of characters and we consider a
    module type for characters. We need three operations on
    characters:
    - is_open that indicates whether a character is an opening
      bracket,
    - is_close that indicates whether a character is a closing
      bracket,
    - are_matched that indicates whether two characters are matching
      brackets. *)

Module Type CHAR.
  Parameter t : Type.
  Parameter is_open: t->bool.
  Parameter is_close: t->bool.
  Parameter are_matched: t->t->bool.
  Axiom not_open_close:
    forall c, is_open c = true -> is_close c = false.
  Axiom not_close_open:
    forall c, is_close c = true -> is_open c = false.
  Axiom matched_open_close:
    forall c c', are_matched c c' = true ->
            is_open c = true /\ is_close c' = true.
End CHAR.

(** ** An Efficient Bracket Matching Algorithm *)

Module Make(Import Char: CHAR).

  Definition is_empty `(xs:list A) : bool :=
    match xs with
    | [] => true
    | _  => false
    end.
  
  Fixpoint bm_spec (s:list Char.t)(cs: list Char.t) : bool :=
    match cs with
    | [ ] => is_empty s
    | c::cs =>
      if is_open c
      then bm_spec (c::s) cs
      else if is_close c
           then match s with
                | [] => false
                | c'::s' => if are_matched c' c then bm_spec s' cs else false
                end
           else bm_spec s cs
    end.

  Definition g1 c s : bool  :=
    if is_open c
    then true
    else if is_close c
         then match s with
              | [] => false
              | c'::s => are_matched c' c
              end
         else true.

  Definition g2 c s :=
    if is_open c
    then c::s
    else if is_close c
         then List.tl s
         else s.
  
  Fixpoint bm1 s cs : bool :=
    match cs with
    | [] => is_empty s
    | c::cs => (g1 c s) && (bm1 (g2 c s) cs)
    end.

  #[export] Instance opt_bm1 s : Opt (bm_spec s)(bm1 s).
  Proof.
    constructor; intros cs; generalize s; clear s; induction cs as [ | c cs IH ]; intro s.
    - trivial.
    - simpl; unfold g1, g2.
      destruct (is_open c); destruct(is_close c); try now rewrite IH.
      destruct s as [ | c' s' ]; auto; now rewrite IH.
  Qed.

  Module Stack.

    Unset Implicit Arguments.
    
    Record t := mk
      { data: list Char.t;
        pu: N;
        po: N;
        inv: pu = length data }.
    
    Set Implicit Arguments.

    Fact stack_eq:
      forall s1 s2 pu1 pu2 po1 po2 inv1 inv2,
        s1 = s2 ->
        pu1 = pu2 ->
        po1 = po2 ->
        mk s1 pu1 po1 inv1 = mk s2 pu2 po2 inv2.
    Proof.
      intros s1 s2 pu1 pu2 po1 po2 inv1 inv2 Hs Hu Ho.
      now subst.
    Qed.

    Definition empty : t := mk [] 0 0 eq_refl.
    
    Definition is_empty (s:t) : bool :=
      match s with
      | mk [] 0 0 _ => true
      | _ => false
      end.

    Fact length_cons_eq:
      forall A (x:A) xs n,
        n = length xs -> N.succ n = length(x::xs).
      intros A x xs n H; simpl; rewrite H; lia.
    Qed.

    Definition push c s : t :=
      match s with
      | mk cs npush npop H => mk (c::cs) (N.succ npush) npop (length_cons_eq _ _ H)
      end.

    Definition pop (s:t) : t.
      refine(
          match s with
          |mk [] 0 npop H => mk [] 0 (N.succ npop) H
          |mk (c::cs) npush  npop H => mk cs (npush-1) (N.succ npop) _
          | _ => _
          end).
      - discriminate.
      - simpl in H; rewrite H; lia.
    Defined.

    Definition of_list cs : t :=
      mk cs (length cs) 0 eq_refl.
    
  End Stack.

  Definition g1' c (s:Stack.t) : bool  :=
    if is_open c
    then true
    else if is_close c
         then match s with  
              | Stack.mk []  _  _ _ => false
              | Stack.mk (c'::s) _ _ _ => are_matched c' c
              end
         else true.
  
  Definition otimes (s s': Stack.t) : Stack.t.
    refine( 
        match (s', s) with
        | (Stack.mk cs1 n1 m1 inv1, Stack.mk cs2 n2 m2 inv2) =>
          Stack.mk
            (if n2 <=? m1 then cs1 else cs1++(skipn m1 cs2))
            (if n2 <=? m1 then n1 else n1+(n2-m1))
            (if n2 <=? m1 then (m1 - n2) + m2 else m2)
            _
        end).
    destruct(n2 <=? m1) eqn:Hle; auto.
    autorewrite with length.
    rewrite <- inv1, <- inv2.
    lia.
  Defined.

  Infix "⊗" := otimes (at level 70).

  #[export] Instance otimes_monoid: Monoid otimes Stack.empty.
  Proof.
    repeat constructor.
    - intros [s1 pu1 po1 inv1] [s2 pu2 po2 inv2] [s3 pu3 po3 inv3]; unfold otimes; simpl.
      apply Stack.stack_eq; destruct(pu1 <=? po2) eqn:H1;destruct(pu2 <=? po3) eqn:H2;
        destruct( pu2 + (pu1 - po2) <=? po3) eqn:H3; destruct(pu1 <=? po3 - pu2 + po2) eqn:H4;
          simpl; try rewrite H1; try rewrite H2; simpl; trivial;
            repeat match goal with
                   | [ H: _ <=? _ = true   |- _] => apply N.leb_le in H
                   | [ H: _ <=? _ = false  |- _] => apply N.leb_nle in H; apply N.nle_gt in H
                   end;
            try (lia); subst.
      + now rewrite skipn_app2, skipn_skipn by (lia).
      + now rewrite skipn_app1, List.app_assoc by (lia).
    - intros [s1 pu1 po1 inv1]; unfold otimes; simpl.
      assert(0 <=? po1 = true) as Hcond
          by (apply N.leb_le; lia).
      rewrite Hcond; f_equal; lia.
    - intros [ [ | c1 s1 ] pu1 po1 inv1].
      + unfold otimes, Stack.empty; now rewrite inv1.
      + unfold otimes, Stack.empty; subst. 
        assert(length(c1::s1) <=? 0 = false) as Hcond
            by (apply N.leb_nle; apply N.nle_gt; autorewrite with length; lia).
        rewrite Hcond; simpl; apply Stack.stack_eq; trivial; lia.
  Qed.
  
  Definition g3 c : Stack.t :=
    if is_open c
    then Stack.push c Stack.empty
    else if is_close c
         then Stack.pop Stack.empty
         else Stack.empty.

  Definition g2' c s :=
    s ⊗ (g3 c).

  Fixpoint bm2 (s:Stack.t) cs :=
    match cs with
    | [] => Stack.is_empty s
    | c::cs => andb (g1' c s) (bm2 (g2' c s) cs)
    end.

  Fact bm2_pi:
    forall cs s s' pu pu' po po' H H',
      s = s' ->
      pu = pu' ->
      po = po' ->
      bm2 (Stack.mk s pu po H)  cs =
      bm2 (Stack.mk s' pu' po' H') cs.
  Proof.
    intros cs s s' pu pu' po po' H H' H0 H1 H2; now subst.
  Qed.

  Lemma bm1_bm2_eq:
    forall cs s,
      bm1 s cs = bm2 (Stack.of_list s) cs.
  Proof.
    induction cs as [ | c cs' IHcs ]; destruct s as [ | c' s' ]; trivial.
    - simpl; rewrite IHcs; unfold g1, g1', g2, g2', g3, otimes.
      destruct (is_open c) eqn:HO; destruct(is_close c) eqn:HC; simpl; trivial.
      + apply Char.not_open_close in HO; rewrite HO in HC; discriminate.
      + now apply bm2_pi.
    - simpl; rewrite IHcs; unfold g1, g1', g2, g2', g3, otimes; simpl.
      destruct (is_open c) eqn:HO; destruct(is_close c) eqn:HC; trivial.
      + apply Char.not_open_close in HO; rewrite HO in HC; discriminate.
      + apply bm2_pi;
        destruct(N.succ(length s') <=? 0) eqn:H; auto;
          try apply N.leb_le in H; try (lia).
        autorewrite with length. lia.
      + assert(forall n, N.succ(N.succ n) <=? 1 = false) as Hcond
            by (intro;apply N.leb_nle; apply N.nle_gt; lia).
        f_equal; unfold Stack.of_list; apply bm2_pi;
          destruct s'; auto; simpl; rewrite Hcond; trivial.
        lia.
      + f_equal; simpl; unfold Stack.of_list.
        assert(forall n, N.succ n <=? 0 = false) as Hcond
            by (intro;apply N.leb_nle; apply N.nle_gt; lia).
        rewrite Hcond; apply bm2_pi; trivial; autorewrite with length.
        lia.
  Qed.

  #[export] Instance opt_bm2 s:
    Opt (bm1 s)(bm2 (Stack.of_list s)).
  Proof.
    constructor; intro; apply bm1_bm2_eq.
  Qed.

  #[export] Instance bm2_accumulate s:
    Opt (bm2 s)(accumulate Stack.is_empty (prod_curry g1') g3 andb otimes s).
  Proof.
    constructor; intro cs; generalize s; clear s;
      induction cs as [ | c cs IH]; intro s.
    - trivial.
    - simpl; f_equal; now rewrite IH.
  Qed.
    
End Make.

Close Scope N_scope.
