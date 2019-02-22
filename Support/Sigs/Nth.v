Require Import Coq.Lists.List Arith Omega Program. Import ListNotations.
Require Import SyDPaCC.Support.List.

(** A strong version of [nth]. *)

Module Sig.

  Program Fixpoint nth {A:Type} (l:list A) (pos:nat | pos < length l) : A := 
    match l with 
      | [] => _
      | a::l => 
        if eq_nat_dec (`pos) 0 
        then a 
        else nth l (pred (`pos))
    end.
  Next Obligation. simpl in *; omega. Qed.
  Next Obligation. simpl in *; omega. Qed.

  Lemma nth_spec : 
    forall (A:Type) (l:list A)  (pos:nat | pos<length l) (default : A), 
      nth l pos = List.nth (`pos) l default.
  Proof.
    induction l; intros [pos Hpos] default; simpl in Hpos.
    - omega.
    - destruct pos; trivial.
      simpl. erewrite IHl. trivial.
  Qed.

  Lemma nth_pi : 
    forall (A:Type)(l :list A) (pos1 pos2: {n:nat | n < length l}),
      `pos1 =  ` pos2 ->
      nth l pos1 = nth l pos2.
  Proof.
    intros A l [pos1 Hpos1] [pos2 Hpos2] H; simpl in H; subst.
    destruct l.
    - simpl in Hpos1. omega.
    - now repeat rewrite nth_spec with (default := a).
  Qed.

  Program Lemma nth_In : 
    forall (A:Type) (l:list A) (pos:nat | pos < length l),
      In (nth l pos) l.
  Proof.
    intros A l [pos Hpos]; subst.
    destruct l as [ | x xs].
    - simpl in Hpos; omega.
    - rewrite nth_spec with (default:=x).
      now apply List.nth_In.
  Qed.

  Lemma In_nth:
    forall (A:Type) (l:list A)(a:A),
      In a l -> exists pos, a = nth l pos.
  Proof.
    induction l as [|x xs IH]; intros a H.
    - contradiction.
    - destruct H as [H|H]; subst.
      + assert(0 < length(a::xs)) as H0 by (simpl; auto with arith).
        exists(exist (fun n=>n<length(a::xs)) 0 H0).
        trivial.
      + destruct(IH a H) as [[pos Hpos] Hnth].
        assert(S pos < length(x::xs)) as HSpos by (simpl; omega).
        exists(exist (fun n=>n<length (x::xs)) (S pos) HSpos).
        rewrite Hnth; repeat rewrite nth_spec with (default:=a).
        trivial.
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
    intuition; subst; trivial.
  Qed.
  Arguments length_sig [A B l l'] _ n.

  Lemma nth_eq : 
    forall (A:Type)(l l':list A)(H:length l = length l'),
      (forall (pos:nat|pos<length l), nth l pos =
                                      nth l' (cast_sig pos (length_sig H))) -> 
      l = l'.
  Proof.
    induction l as [|x xs IH]; destruct l' as [|x' xs'];intros Hlen H;
    trivial; try discriminate.
    assert(x = x') as Head.
    {
      assert(0<length (x::xs)) as H0 by (simpl;omega).
      set(pos0:=exist (fun n=>n<_) 0 H0). 
      now specialize (H pos0). 
    }
    assert(length xs = length xs') as Hlen' by auto.
    assert(forall (pos : nat | pos < length xs),
              nth xs pos =
              nth xs' (cast_sig pos (length_sig Hlen'))) as Htail.
    {
      intros [pos Hpos]. 
      assert(S pos<length(x::xs)) as Hpos' by (simpl;omega).
      specialize (H (exist(fun n=>n<_) (S pos) Hpos')). simpl in H.
      match goal with 
        | [ H : nth xs ?pos1 = nth xs' ?pos2 |- _] =>
          transitivity (nth xs pos1)
      end.
      repeat rewrite nth_spec with (default:=x). trivial.
      rewrite H.
      repeat rewrite nth_spec with (default:=x). trivial.
    }
    assert(xs = xs') by (now apply (IH _ Hlen')).
    now f_equal.
  Qed.

  Fact lt_eq: 
    forall {m m':nat}(H:m=m')(n:nat), (n<m) <-> (n<m').
    intros m m' H n; rewrite H; intuition.
  Qed. 

  Lemma nth_map:
    forall (A B : Type) (f : A -> B) (l : list A) pos,
      nth (map f l) pos = f (nth l (cast_sig pos (length_sig (map_length f l)))).
  Proof.
    intros A B f; induction l as [|x xs IH]; intro pos.
    - simpl in pos; destruct pos; omega.
    - destruct pos as [ [ | pos] Hpos].
      + trivial.
      + simpl; rewrite IH; now repeat rewrite nth_spec with (default:=x).
  Qed.     

  Lemma combine_length':
    forall {A B: Type}{l:list A}{l':list B}(H:length l=length l'),
      length(combine l l') = length l.
  Proof.
    intros A B l l' H.
    autorewrite with length. rewrite H.
    auto with arith.
  Qed.

  Lemma combine_length'':
    forall {A B: Type}{l:list A}{l':list B}(H:length l=length l'),
      length(combine l l') = length l'.
  Proof.
    intros A B l l' H.
    autorewrite with length. rewrite H.
    auto with arith.
  Qed.

  Lemma nth_combine:
    forall (A B:Type)(l:list A)(l':list B) pos (H: length l = length l'),
      let H1 := length_sig(combine_length' H) in
      let H2 := length_sig(combine_length'' H) in
      nth (combine l l') pos = (nth l (cast_sig pos H1), 
                                nth l' (cast_sig pos H2)).
  Proof.
    induction l; destruct l'; intros [pos Hpos] H; try (simpl in *; omega).
    simpl (combine (a::l) (b::l')).  
    destruct pos.
    - trivial.
    - assert(length l = length l') as Hlen by auto.
      simpl; rewrite (IHl _ _ Hlen).
      f_equal; now apply nth_pi.
  Qed.

End Sig.