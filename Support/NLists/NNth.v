Require Import Coq.Lists.List Arith Omega Program. Import ListNotations.
From SyDPaCC.Support Require Import Sigs.Map NLists.NLength.

Open Scope N_scope.

Set Implicit Arguments.

Function nth (A:Type) (pos:N) (l:list A) (default:A) : A :=
  match l with
  | [ ]  => default
  | a::l => match pos with
           | 0 => a
           | _ => nth (N.pred pos) l default
           end
  end.

Lemma nth_map :
  forall A B pos l default fdefault (f:A->B),
    pos < length l ->
    fdefault = f default -> 
    nth pos (map f l) fdefault =
    f (nth pos l default).
Proof.
  intros A B; induction pos as [ | pos IH] using N.peano_ind;
    intros l default b f  Hlt Hdef.
  - destruct l as [ | a l].
    + now rewrite nth_equation.
    + trivial.
  - rewrite nth_equation; destruct l as [ | a l]; simpl.
    + trivial.
    + destruct (N.succ pos) eqn:Heq; auto.
      rewrite <- Heq, N.pred_succ in *.
      rewrite length_cons in Hlt; subst.
      apply IH; auto; zify; omega.
Qed.
    
Module Sig.

  (** A strong version of [nth]. *)
  
  Program Fixpoint nth {A:Type} (l:list A) (pos:N | pos < length l) : A := 
    match l with 
      | [] => _
      | a::l => 
        if N.eq_dec (`pos) 0 
        then a 
        else nth l (N.pred (`pos))
    end.
  Next Obligation. simpl in *; zify; omega. Qed.
  Next Obligation.
    replace (length(a::l)) with (1 + length l)in H0  by auto.
    assert(N.pred pos < pos) by now apply N.lt_pred_l.
    zify; omega.
  Qed.

  Lemma nth_spec : 
    forall (A:Type) (l:list A)  (pos:N | pos<length l) (default : A), 
      nth l pos = List.nth (N.to_nat (`pos)) l default.
  Proof.
    induction l; intros [pos Hpos] default.
    - contradict Hpos; simpl; zify; omega.
    - destruct pos using N.peano_ind; trivial.
      simpl; rewrite Nnat.N2Nat.inj_succ.
      destruct(N.eq_dec (N.succ pos) 0) as [ Hl | Hr ].
      + contradict Hl; zify; omega.
      + rewrite IHl with (default:=default); simpl.
        f_equal; now rewrite N.pred_succ.
  Qed.
  
  Lemma nth_pi : 
    forall (A:Type)(l :list A) (pos1 pos2: {n:N | n < length l}),
      `pos1 =  ` pos2 ->
      nth l pos1 = nth l pos2.
  Proof.
    intros A l [pos1 Hpos1] [pos2 Hpos2] H; simpl in H; subst.
    destruct l.
    - simpl in Hpos1; contradict Hpos1; zify; omega.
    - now repeat rewrite nth_spec with (default := a).
  Qed.

  Program Lemma nth_In : 
    forall (A:Type) (l:list A) (pos:N | pos < length l),
      In (nth l pos) l.
  Proof.
    intros A l [pos Hpos]; subst.
    destruct l as [ | x xs].
    - simpl in Hpos; contradict Hpos; zify; omega.
    - rewrite nth_spec with (default:=x).
      assert(length (x::xs) = 1 + length xs) as Heq by auto.
      apply List.nth_In. simpl proj1_sig.
      simpl. apply N.compare_lt_iff in Hpos.
      rewrite Nnat.N2Nat.inj_compare in Hpos.
      apply nat_compare_lt in Hpos.
      rewrite Nlength_length in Hpos.
      rewrite Nnat.Nat2N.id in Hpos.
      auto.
  Qed.

  Lemma In_nth:
    forall (A:Type) (l:list A)(a:A),
      In a l -> exists pos, a = nth l pos.
  Proof.
    induction l as [|x xs IH]; intros a H.
    - contradiction.
    - destruct H as [H|H]; subst.
      + assert(0 < length(a::xs)) as H0
            by (autorewrite with length; zify; omega).
        exists(exist (fun n=>n<length(a::xs)) 0 H0).
        trivial.
      + destruct(IH a H) as [[pos Hpos] Hnth].
        assert(N.succ pos < length(x::xs)) as HSpos
          by (autorewrite with length; now apply N.add_lt_mono_l).
        exists(exist (fun n=>n<length (x::xs)) (N.succ pos) HSpos).
        rewrite Hnth; repeat rewrite nth_spec with (default:=a).
        simpl. now rewrite Nnat.N2Nat.inj_succ.
  Qed.

  Definition cast {A B:Type}(a:A)(H:A=B) : B.
    rewrite <- H.
    assumption.
  Defined.

  Definition cast_sig {A:Type}{P P':A->Prop}(a:sig P)(H:forall a, P a<->P' a) : sig P'.
    destruct a as [a Ha].
    apply H in Ha.
    exact(exist _ a Ha).
  Defined.

  Lemma length_sig:
    forall A B (l:list A)(l':list B),
      length l = length l' -> forall n,  n < length l <-> n < length l'.
    intuition; subst; [ rewrite <- H | rewrite H]; trivial.
  Qed.
  Arguments length_sig [A B l l'] _ n.

  Lemma nth_eq : 
    forall (A:Type)(l l':list A)(H:length l = length l'),
      (forall (pos:N|pos<length l), nth l pos =
                                      nth l' (cast_sig pos (length_sig H))) -> 
      l = l'.
  Proof.
    induction l as [|x xs IH]; destruct l' as [|x' xs'];intros Hlen H; trivial.
    - clear H; apply length_nil in Hlen. now exfalso.
    - clear H; symmetry in Hlen; apply length_nil in Hlen. now exfalso.
    - assert(x = x') as Head.
      {
        assert(0<length (x::xs)) as H0
            by (autorewrite with length; zify; omega).
        set(pos0:=exist (fun n=>n<_) 0 H0). 
        now specialize (H pos0). 
      }
      assert(length xs = length xs') as Hlen'.
      {
        clear H. 
        autorewrite with length in Hlen.
        zify; omega.
      }
      assert(forall (pos : N | pos < length xs),
                nth xs pos =
                nth xs' (cast_sig pos (length_sig Hlen'))) as Htail.
      {
        intros [pos Hpos]. 
        assert(N.succ pos<length(x::xs)) as Hpos'
            by (autorewrite with length; zify; omega).
        specialize (H (exist(fun n=>n<_) (N.succ pos) Hpos')).
        repeat rewrite nth_spec with (default:=x) in H. simpl proj1_sig in H.
        rewrite Nnat.N2Nat.inj_succ in H; simpl in H.
        repeat rewrite nth_spec with (default:=x). simpl.
        eassumption.
      }
    assert(xs = xs') by (now apply (IH _ Hlen')).
    now f_equal.
  Qed.    

  Fact lt_eq: 
    forall {m m':N}(H:m=m')(n:N), (n<m) <-> (n<m').
    intros m m' H n; rewrite H; intuition.
  Qed. 

  Lemma nth_map:
    forall (A B : Type) (f : A -> B) (l : list A) pos,
      nth (map f l) pos = f (nth l (cast_sig pos (length_sig (map_length f l)))).
  Proof.
    intros A B f; induction l as [|x xs IH]; intro pos.
    - simpl in pos; destruct pos as [pos H]; contradict H; zify; omega.
    - destruct pos as [ [ | pos] Hpos].
      + trivial.
      + simpl; rewrite IH; now repeat rewrite nth_spec with (default:=x).
  Qed.     

  Hint Rewrite combine_length : length.
  
  Lemma combine_length':
    forall {A B: Type}{l:list A}{l':list B}(H:length l=length l'),
      length(combine l l') = length l.
  Proof.
    intros A B l l' H.
    repeat rewrite Nlength_length in *; f_equal.
    apply Nnat.Nat2N.inj in H.
    autorewrite with length. rewrite H.
    auto with arith.
  Qed.

  Lemma combine_length'':
    forall {A B: Type}{l:list A}{l':list B}(H:length l=length l'),
      length(combine l l') = length l'.
  Proof.
    intros A B l l' H.
    repeat rewrite Nlength_length in *; f_equal.
    apply Nnat.Nat2N.inj in H.
    autorewrite with length. rewrite H.
    auto with arith.
  Qed.

  Hint Rewrite @combine_length' @combine_length'' : length.

  Lemma nth_combine:
    forall (A B:Type)(l:list A)(l':list B) pos (H: length l = length l'),
      let H1 := length_sig(combine_length' H) in
      let H2 := length_sig(combine_length'' H) in
      nth (combine l l') pos = (nth l (cast_sig pos H1), 
                                nth l' (cast_sig pos H2)).
  Proof.
    induction l as [ | a l IH]; destruct l' as [ | b l'];
      intros [pos Hpos] H;
      try (simpl in Hpos; contradict Hpos; zify; omega).
    simpl (combine (a::l) (b::l')).  
    destruct pos.
    - trivial.
    - assert(length l = length l') as Hlen.
      {
        autorewrite with length in H.
        now apply N.add_cancel_l in H.
      }
      simpl; rewrite (IH _ _ Hlen).
      f_equal; now apply nth_pi.
  Qed.

  Lemma map_length:
    forall {A:Type}{P:A->Prop}(l:list A) (H:forall a,In a l->P a),
      length(Sig.map l H) = length l.
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
      nth (Sig.map l H) pos =
      exist P x (H x (nth_In l pos')).
  Proof.
    intros A P l H UIP0 pos H' pos' res.
    unfold res, pos', H' in *. clear H' pos' res.
    generalize dependent l. 
    induction l as [|x xs IH]; intros H [pos Hpos].
    - simpl in Hpos; contradict Hpos; zify; omega.
    - destruct pos using N.peano_ind.
      + simpl. f_equal. apply UIP0.      
      + assert(exists H, N.eq_dec (N.succ pos) 0 = right H) as Heq.
        {
          clear.
          destruct(N.eq_dec (N.succ pos) 0) as [ Hl | Hr ].
          - contradict Hl; zify; omega.
          - exists Hr. reflexivity.
        }
        destruct Heq as [ Hdiff Heq].
        simpl.
        rewrite Heq at 1.
        rewrite IH.
        assert(forall a b:sig P, proj1_sig a = proj1_sig b -> a = b) 
          as Hinj 
            by
              (intros [a Ha] [b Hb] H0; simpl in H0; subst;
               assert(Ha = Hb) by apply UIP0; now subst).
        apply Hinj; simpl; rewrite Heq.
        now apply nth_pi.
  Qed.

End Sig.

Hint Rewrite @Sig.map_length : length.

Close Scope N_scope.