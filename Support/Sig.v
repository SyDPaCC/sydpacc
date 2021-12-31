Require Import Coq.Lists.List Arith Lia Program.
Import ListNotations.
Require Import SyDPaCC.Support.List.

(** * List Functions using [sig] *)

(** ** [nth] with a precondition on the index *)

Program Fixpoint nth {A:Type} (l:list A) (pos:nat | pos < length l) : A := 
  match l with 
  | [] => _
  | a::l => 
    if eq_nat_dec (`pos) 0 
    then a 
    else nth l (pred (`pos))
  end.
Next Obligation. simpl in *; lia. Qed.
Next Obligation. simpl in *; lia. Qed.

Lemma nth_spec : 
  forall (A:Type) (l:list A)  (pos:nat | pos<length l) (default : A), 
    nth l pos = List.nth (`pos) l default.
Proof.
  induction l; intros [pos Hpos] default; simpl in Hpos.
  - lia.
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
  - simpl in Hpos1. lia.
  - now repeat rewrite nth_spec with (default := a).
Qed.

Program Lemma nth_In : 
  forall (A:Type) (l:list A) (pos:nat | pos < length l),
    In (nth l pos) l.
Proof.
  intros A l [pos Hpos]; subst.
  destruct l as [ | x xs].
  - simpl in Hpos; lia.
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
      assert(S pos < length(x::xs)) as HSpos by (simpl; lia).
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
  lia; subst; trivial.
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
    assert(0<length (x::xs)) as H0 by (simpl;lia).
    set(pos0:=exist (fun n=>n<_) 0 H0). 
    now specialize (H pos0). 
  }
  assert(length xs = length xs') as Hlen' by auto.
  assert(forall (pos : nat | pos < length xs),
            nth xs pos =
            nth xs' (cast_sig pos (length_sig Hlen'))) as Htail.
  {
    intros [pos Hpos]. 
    assert(S pos<length(x::xs)) as Hpos' by (simpl;lia).
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
  - simpl in pos; destruct pos; lia.
  - destruct pos as [ [ | pos] Hpos].
    + trivial.
    + simpl; rewrite IH; now repeat rewrite nth_spec with (default:=x).
Qed.     

Lemma nth_combine:
  forall (A B:Type)(l:list A)(l':list B) pos (H: length l = length l'),
    let H1 := length_sig(combine_length' H) in
    let H2 := length_sig(combine_length'' H) in
    nth (combine l l') pos = (nth l (cast_sig pos H1), 
                              nth l' (cast_sig pos H2)).
Proof.
  induction l; destruct l'; intros [pos Hpos] H; try (simpl in *; lia).
  simpl (combine (a::l) (b::l')).  
  destruct pos.
  - trivial.
  - assert(length l = length l') as Hlen by auto.
    simpl; rewrite (IHl _ _ Hlen).
    f_equal; now apply nth_pi.
Qed.

(** * A [map] function that attaches a property proof to each element *)

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
  - simpl in Hpos; lia.
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

#[export] Hint Rewrite @map_length : length.

