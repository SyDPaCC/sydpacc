Require Import Coq.Lists.List Program Omega.
Import ListNotations.
From SyDPaCC Require Import Support.Lists.Length Support.Sigs.Nth.

Module Sig.

  Program Fixpoint map (A:Type)(P:A->Prop)(l:list A)(H:forall a,List.In a l->P a) : 
    list (sig P) :=
    match l with 
      | [] => []
      | x::xs => (exist P x (H x _))::(map _ _ xs _)
    end.
  Next Obligation.
    simpl; auto.
  Qed.
  Next Obligation.
    apply H. simpl. auto.
  Qed.

  Arguments map [A P] l H.

  Lemma map_pi:
    forall (A:Type)(P:A->Prop)(l l':list A)(H:forall a,List.In a l->P a)
           (H':forall a,List.In a l'->P a)
           (Inj:forall a a': sig P,  proj1_sig a = proj1_sig a' -> a = a'),
      l = l' -> map l H = map l' H'.
  Proof.
    intros A P l l'; generalize l; clear l; induction l' as [ | x xs IH]; intros l H H' Inj Heq; subst.
    - trivial.
    - simpl; erewrite IH; f_equal; trivial.
      now apply Inj.
  Qed.
    
  Fact map_app_1 :
    forall {A:Type}{P:A->Prop}{l l':list A},
      (forall a,List.In a (l++l')->P a) ->
      forall a, List.In a l -> P a.
    intuition.
  Qed.

  Fact map_app_2 :
    forall {A:Type}{P:A->Prop}{l l':list A},
      (forall a,List.In a (l++l')->P a) ->
      forall a, List.In a l' -> P a.
    intuition.
  Qed.

  Lemma map_app:
    forall {A:Type}{P:A->Prop}(l l':list A)(H:forall a,List.In a (l++l')->P a),
      (forall a a': sig P,  proj1_sig a = proj1_sig a' -> a = a') ->
      map (l++l') H = map l (map_app_1 H) ++ (map l' (map_app_2 H)).
  Proof.
    intros A P; induction l as [ | x xs IH]; intros l' Hin Hinj.
    - now apply map_pi.
    - simpl; f_equal.
      + now apply Hinj.
      + rewrite IH by trivial; f_equal; now apply map_pi.
  Qed.    
    
  Lemma in_map_in:
    forall {A:Type}{P:A->Prop}(l:list A)(H:forall a,List.In a l->P a),
    forall (a:sig P), In a (map l H) -> In (proj1_sig a) l.
  Proof.
    intros A P; induction l as [ | x xs IH]; intros Hl a H.
    - trivial.
    - simpl in H; destruct H as [H|H].
      + left; rewrite <- H; trivial.
      + right; firstorder.
  Qed.

    Lemma in_in_map:
      forall {A:Type}{P:A->Prop}(l:list A)(H:forall a,List.In a l->P a),
        (forall a a': sig P,  proj1_sig a = proj1_sig a' -> a = a') ->
        forall (a:sig P), In (proj1_sig a) l -> In a (map l H).
  Proof.
    intros A P; induction l as [ | x xs IH]; intros Hl Hinj a H.
    - trivial.
    - simpl in H; destruct H as [H|H].
      + left. now apply Hinj.
      + right; firstorder.
  Qed.

  Lemma map_proj1_sig :
    forall {A}{P:A->Prop}(l:list A)(H:forall a,List.In a l->P a),
      List.map (@proj1_sig A P) (map l H) = l.
  Proof.
    intros A P; induction l as [|x xs IH]; intro H.
    - trivial.
    - simpl; rewrite IH; trivial.
  Qed.
  
  Lemma map_length:
    forall {A:Type}{P:A->Prop}(l:list A) (H:forall a,In a l->P a),
      length(map l H) = length l.
  Proof.
    induction l as [|x xs IH]; intro H.
    - auto.
    - simpl; rewrite IH; auto.
  Qed.

  Lemma map_nth:
    forall {A:Type}(P:A->Prop)(l:list A)(H:forall a,In a l->P a)
           (UIP:forall a (H1:P a)(H2:P a), H1=H2) pos,
      let H' := Sig.length_sig (map_length l H) in
      let pos' := Sig.cast_sig pos H' in
      let x := Sig.nth l pos' in
      Sig.nth (map l H) pos =
      exist P x (H x (Sig.nth_In _ l pos')).
  Proof.
    intros A P l H UIP0 pos H' pos' res.
    unfold res, pos', H' in *. clear H' pos' res.
    generalize dependent l. 
    induction l as [|x xs IH]; intros H [pos Hpos].
    - simpl in Hpos; omega.
    - destruct pos.
      + simpl. f_equal. apply UIP0.
      + simpl. repeat rewrite IH by assumption.
        simpl; f_equal.
        assert(forall a b:sig P, proj1_sig a = proj1_sig b -> a = b) 
          as Hinj 
            by
              (intros [a Ha] [b Hb] H0; simpl in H0; subst;
               assert(Ha = Hb) by apply UIP0; now subst).
        apply Hinj; auto.
        now apply Sig.nth_pi.
  Qed.

End Sig.

Hint Rewrite @Sig.map_length : length.

