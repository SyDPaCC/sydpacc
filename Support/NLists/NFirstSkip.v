Require Import Coq.Lists.List NArith Omega. Import ListNotations.
From SyDPaCC.Support.NLists Require Export NLength NSeq NNth.

Set Implicit Arguments.

Open Scope N_scope.

Function skipn A n (l:list A) : list A :=
  match n with
  | 0 => l
  | n => match l with
        | [ ]  => [ ]
        | _::l => skipn (N.pred n) l
        end
  end.

Function firstn A n (l:list A) : list A :=
  match n with
  | 0 => [ ]
  | n => match l with
        | [ ]  => [ ]
        | a::l => a :: firstn (N.pred n) l
        end
  end.

(** skipn [l] has  length |[l]|-n *)
Lemma skipn_length:
  forall A (l: list A) n, length (skipn n l) = length l - n.
Proof.
  intros A l n; generalize dependent l; induction n as [ | n IH ] using N.peano_ind; intro l; simpl.
  - rewrite skipn_equation; zify; omega.
  - rewrite skipn_equation.
    destruct(N.succ n) eqn:Heq.
    + zify; omega.
    + destruct l as [ | a l IHl ].
      * trivial.
      * rewrite <- Heq, N.pred_succ, IH.
        rewrite length_cons, N.add_1_l, N.sub_succ.
        trivial.
Qed.

(** [skipn nil] is [nil] *)
Fact skipn_nil: forall A n, @skipn A n [ ] = [ ].
Proof.
  intros A n; destruct n; reflexivity.
Qed.

(** [skipn  (length l) l] is [nil] *)
Fact skipn_length_l:
  forall A (l:list A), skipn (length l) l = nil.
Proof.
  induction l; repeat (rewrite skipn_equation, length_cons, N.add_1_l, N.pred_succ); auto.
  destruct(N.succ (length l)) eqn:Heq.
  - apply N.succ_0_discr in Heq. now exfalso.
  - trivial.
Qed.

Hint Rewrite skipn_length skipn_length_l: length.

(** [firstn nil] is [nil] *)
Fact firstn_nil:
  forall A n, @firstn A n [ ] = [ ].
Proof.
  intros A n; destruct n; trivial.
Qed.

(** [firstn] commutes with [map] *)
Fact firstn_map:
  forall A B n l (f:A->B),
    firstn n (map f l) = map f (firstn n l).
Proof.
  intros A B n. induction n as [ | n IH] using N.peano_ind; intros l f.
  - repeat rewrite firstn_equation; trivial.
  - repeat rewrite firstn_equation.
    repeat rewrite <- N.succ_pos_spec;
      repeat rewrite N.succ_pos_spec, N.pred_succ.
    destruct l; simpl; auto.
    now rewrite IH.
Qed.

Fact firstn_seq:
  forall n first size,
    firstn n (seq first size) = seq first (N.min n size).
Proof.
  induction n as [ | n IH ] using N.peano_ind; intros first size.
  - rewrite N.min_0_l. now rewrite firstn_equation, seq_equation.
  - repeat rewrite firstn_equation.
    repeat rewrite <- N.succ_pos_spec;
      repeat rewrite N.succ_pos_spec, N.pred_succ.
    destruct size.
    + rewrite N.min_0_r.
      now repeat rewrite seq_equation.
    + rewrite seq_equation, IH.
      rewrite <- N.succ_pos_pred, N.pred_succ, <- N.succ_min_distr.
      rewrite seq_equation with (size:=N.succ _ ).
      destruct  (N.min n (Pos.pred_N p)); simpl; auto.
      now rewrite Pos.pred_N_succ.
Qed.  
      
(*

(** [firstn  (length l) l] is [l] *)
Lemma firstn_length_l: forall (l:list A), firstn (length l) l = l.
  Proof.
    induction l.
    auto.
    simpl.
    f_equal.
    assumption.
  Qed.


  (** [length (firstn n l) + length (skipn n l) = length l] *)
  Lemma firstn_skipn_length: forall n (l: list A), 
    length (firstn n l) + length (skipn n l) = length l.
  Proof.
    intros. rewrite <- app_length. rewrite firstn_skipn. reflexivity.
  Qed.
  
  (** length of [firstn n l] written with length of [l] *)
  Lemma firstn_length: forall (l: list A) (n: nat), 
    length (firstn n l) = min n (length l).
  Proof.
    intros.
    assert (length (firstn n l) = length l - length (skipn n l)).
    apply plus_minus. rewrite plus_comm. symmetry. apply firstn_skipn_length.
    rewrite H. rewrite skipn_length.
    symmetry. rewrite min_comm. apply min_minus.
  Qed.

  (** length of [firstn n l] when [n] is lesser than length of [l] *)
  Lemma firstn_length1: 
    forall (l: list A) (n: nat),
      n <= length l -> length (firstn n l) = n.
  Proof.
    intros. rewrite firstn_length. apply min_l. assumption.
  Qed.
  
  (** compositions of [skipn]  *)
  Lemma skipn_compose: 
    forall (l: list A) (n: nat) (m: nat),
      skipn n (skipn m l) = skipn (n+m) l.
  Proof.
    intros l.
    induction l. symmetry. rewrite skipn_nil. symmetry. rewrite skipn_nil. apply skipn_nil.
    intros n m. destruct m. rewrite plus_0_r. simpl. reflexivity.
    simpl (skipn (S m) (a::l)).
    replace (n + S m) with (S(n + m)).
    simpl skipn at 3. apply IHl.
    auto with arith.
  Qed.


  (** [k]th element of [firstn n  l] is [k]th element of [l] if [k] is lesser than [n] *)
  Lemma firstn_nth: 
    forall (l:list A) (n k:nat) (d:A),
      k < n -> nth k (firstn n l) d = nth k l d.
  Proof.
    induction l.
    intros. rewrite firstn_nil. reflexivity.
    intros. destruct n. absurd (k<0). omega. assumption.
    destruct k. simpl. reflexivity.
    simpl. apply IHl. omega.
  Qed.

  (** [k]th element of [skipn n  l] is [(k+n)]th element of [l] if [k] is lesser than [(length l - n)] *)
  Lemma skipn_nth: 
    forall (l:list A) (n k: nat) (d:A),
      k < length l - n -> nth k (skipn n l) d = nth (k+n) l d.
  Proof.
    induction l.
    intros. simpl in H. absurd (k<0). omega. assumption.
    intros. destruct n. rewrite plus_0_r. simpl. reflexivity.
    destruct k. simpl. change n with (0+n). apply IHl. simpl in H. assumption.
    simpl. rewrite <- plus_Snm_nSm. apply IHl.
    simpl in H.
    assumption.
  Qed.

  (** [firstn] of reverse of [l] is reverse of [skipn (length l - n) l]*)
  Lemma firstn_rev': 
    forall (l:list A) (n:nat),
      firstn n (rev' l) = rev' (skipn (length l - n) l).
  Proof.
    intros.
    destruct l. simpl. apply firstn_nil.
    apply nthSameLengthEqual with (d:=a).
    rev'_to_rev.
    rewrite rev_length.
    rewrite skipn_length.
    rewrite firstn_length.
    rewrite rev_length.
    rewrite min_comm. apply min_minus.

    intros.
    rev'_to_rev.
    rev'_to_rev in H. 
    rewrite firstn_length in H.
    rewrite rev_length in H.
    assert (n0 < n). apply lt_le_trans with (m:=min n (length (a::l))). assumption. apply le_min_l.
    assert (n0 < length (a::l)). apply lt_le_trans with (m:=min n (length (a::l))). assumption. apply le_min_r.
    repeat (rewrite firstn_nth || rewrite rev_nth || rewrite skipn_nth || rewrite skipn_length).
    f_equal. 
(*     set (n1:= length (a :: l)) in *.  *)
(*     assert (n<=n1 ->n1-(n1-n)=n). omega. *)
(*     assert (n1<n ->n1-(n1-n)=n1). omega. *)
(*     Require Import Compare_dec.     *)
(*     destruct (le_lt_dec n n1) as [l0 | l0] ; [rewrite (H2 l0); clear H2 H3 l0|rewrite (H3 l0); clear H2 H3 l0]. *)
(*     assert (S n0<= n) by (info omega). *)
(*     assert (S n0<= n1) by (info omega). *)
    clear H H1;  omega.
    simpl length.  (simpl in H ;  simpl in H1; clear H; omega). omega. assumption. assumption.
  Qed.

  (* Inverse the compostion of firstn and skipn *)
  Lemma firstn_skipn_inv: 
    forall (l: list A) (n m: nat) (pre: m <= length l),
      firstn n (skipn m l) = skipn m (firstn (m+n) l).
  Proof.
    intro l.
    induction l.
    symmetry. repeat (rewrite skipn_nil || rewrite firstn_nil). reflexivity.
    intros. 
    destruct m. simpl. reflexivity.
    destruct n. simpl. rewrite plus_0_r. 
    assert (length (skipn m (firstn m l)) = 0).
    rewrite skipn_length. rewrite firstn_length.
    simpl in pre. rewrite min_l. auto with arith. auto with arith.
    assert (forall (l: list A), length l = 0 -> l = nil).
    induction l0. simpl. reflexivity. simpl. intro H1. discriminate H1.
    apply H0 in H. symmetry. assumption.
    simpl skipn at 1. simpl firstn at 2. simpl skipn at 2.
    apply IHl. intuition.
  Qed.

  (** [firstn] composition *) 
  Lemma firstn_compose: 
    forall (l: list A) (n n': nat),
    firstn n (firstn n' l) = firstn (min n n') l.
  Proof.
    induction l.
    intros. repeat (rewrite firstn_nil). reflexivity.
    intros n0 n'0. destruct n0. simpl. reflexivity.
    destruct n'0. simpl. reflexivity.
    simpl. f_equal. apply IHl.
  Qed.

  Hint Rewrite  firstn_compose : firstn.
  Hint Resolve firstn_compose :firstn.

   (** [firstn] composition *) 
  Lemma firstn_compose': 
    forall (l: list A) (n : nat),
    firstn n (firstn n l) = firstn n l.
  Proof.
    intros l n.
    rewrite  firstn_compose.
    rewrite min_idempotent.
    reflexivity.
  Qed.
  Hint Rewrite  firstn_compose' : firstn.
  Hint Resolve firstn_compose' :firstn.

  
  Lemma firstlength: 
    forall (l:list A), 
      firstn (length l) l = l.
  Proof.
    induction l.
    auto.
    simpl.
    f_equal. assumption.
  Qed.


  (** [firstn] applied to [l++l'] is equal to firstn applied to [l] if the length of [l] is greater than n  *)
  Lemma firstn_app1:
    forall (l l':list A) (n:nat),
      n <= length l -> firstn n (l++l') = firstn n l.
  Proof.
    induction l as [|a l IHl].
    intros l' n H. destruct n. firstorder.
    simpl in H. absurd (S n <= 0). firstorder. assumption.
    destruct n.
    intros H. simpl. reflexivity.
    intros H. simpl. rewrite IHl. reflexivity. simpl in H. firstorder.
  Qed.

  (** [firstn] applied to [l++l'] is equal to  [l] if the length of [l] is  n  *)
  Lemma firstn_app_length:
    forall (l l':list A) (n:nat),
      n = length l -> firstn n (l++l') = l.
  Proof.
    intros l l' n length_l.
    rewrite  firstn_app1;[|rewrite length_l;auto].
    rewrite length_l.
    rewrite firstlength.
    reflexivity.
  Qed.

  (** [skipn] applied to [l++l'] is equal to skipn applied to [l] append to [l']  if the length of [l] is greater than [n]  *)
  Lemma skipn_app1: 
    forall (l l':list A) (n:nat),
      n <= length l -> skipn n (l++l') = (skipn n l) ++ l'.
  Proof.
    induction l as [|a l IHl].
    intros l' n H. destruct n. firstorder.
    simpl in H. absurd (S n <= 0). firstorder. assumption.
    destruct n.
    intros H. simpl. reflexivity.
    intros H. simpl. rewrite IHl. reflexivity. simpl in H. firstorder.
  Qed.


  (** [firstn] applied to [l++l'] is equal to [l] append to first (n- length l) element of [l'] if the length of [l] is lesser than [n]  *)
  Lemma firstn_app2: 
    forall (l l':list A) (n:nat),
      n >= length l -> firstn n (l++l') = l ++ firstn (n-length l) l'.
  Proof.
    induction l as [|a l IHl].
    intros l' n H. simpl. rewrite <- minus_n_O. reflexivity.
    intros. simpl.
    destruct n.
    simpl in H. absurd (0>=S(length l)). unfold ge. apply le_Sn_O. assumption.
    simpl. f_equal. apply IHl. simpl in H. firstorder.
  Qed.

  (** [skipn] applied to [l++l'] is equal to skip [n - length l] element of [l'] if the length of [l] is lesser than [n]  *)
  Lemma skipn_app2:
    forall (l l':list A) (n:nat),
      n >= length l -> skipn n (l++l') = skipn (n-length l) l'.
  Proof.
    induction l.
    intros. simpl. rewrite <- minus_n_O. reflexivity.
    intros. simpl.
    destruct n.
    simpl in H. absurd (0>=S(length l)). unfold ge. apply le_Sn_O. assumption.
    simpl. apply IHl. simpl in H. firstorder.
  Qed.

  Lemma skipn_app_length:
    forall (l l':list A) (n:nat),
      n = length l -> skipn n (l++l') = l'.
  Proof.
    intros l l' n length_l.
    rewrite  skipn_app2;[|rewrite length_l;auto].
    rewrite length_l.
    replace (length l - length l) with 0 by (auto with arith).
    reflexivity.
  Qed.

  (* A list can be cut in two where the first part is firstn of the list *)
  Lemma firstn_app : forall (A : Type) (l : list A) x, length l > x -> 
    exists l1, exists l2, l1 ++ l2 = l /\ length l1 = x /\
      firstn x l = firstn x l1.
  Proof.
    induction l ; intros ; simpl.
    inversion H.
    destruct x. simpl. exists nil. exists (a :: l). intuition.
    assert (length l > x). simpl in H. intuition.
    destruct (IHl x H0) as [l1 [l2 [IHl1 [IHl2 IHl3]]]]. clear IHl.
    exists (a :: l1). exists l2. subst. simpl. rewrite IHl3. intuition.
  Qed.

  (* if we keep only the first n elements and then skip them we have the nil list *)
  Lemma firstn_skipn_nil : forall (A : Type) a (l : list A), skipn a (firstn a l) = nil.
  Proof.
    induction a ; simpl ; intros.
    reflexivity.
    destruct l.
    reflexivity.
    rewrite IHa. reflexivity.
  Qed.

End  firstnskipn.
Hint Rewrite   firstn_skipn_nil firstlength firstn_app1  firstn_app2 firstn_app_length : firstn.
  Hint Rewrite  firstn_skipn_nil  skipn_app1 skipn_app2 skipn_app_length skipn_length_l skipn_nil  skipn_compose skipn_nth : skipn.

Lemma cutInThree: 
  forall (A:Type)(n:nat)(l:list A),
    n < List.length l ->
    forall (d:A), 
      l = (firstn n l)++(nth n l d)::(skipn (S n) l).
Proof.
  intros A n l H d.
  generalize dependent n.
  induction l.
  intros; simpl in H; contradict H; omega.
  intros; simpl.
  destruct n.
  trivial.
  simpl in *; f_equal; apply IHl; omega. 
Qed.

Lemma cutInFirstnSkipn: 
  forall (A:Type)(n:nat)(l:list A),
    n < List.length l ->
      l = (firstn n l)++(skipn  n l).
Proof.
  intros A n l n_lt_len.
  generalize dependent n.
  induction l.
  intros; simpl in n_lt_len; contradict n_lt_len; omega.
  intros; simpl.
  destruct n.
  trivial.
  simpl in *; f_equal; apply IHl; omega. 
Qed.

Lemma firstnNth: 
  forall (A:Type)(l2 l2' l1 l1':list A)(a:A),
    List.length l1 < List.length l2 ->
    l1++a::l1' = l2 ++ l2' ->
    forall d, nth (List.length l1) l2 d = a.
Proof.
  induction l2; intros l2' l1 l1' x H H0 d.
  simpl in H; contradict H; omega.
  destruct l1; simpl in *.
  inversion H0; auto.
  apply IHl2 with (l1':=l1')(l2':=l2').
  omega.
  inversion H0; auto.
Qed.

Ltac listsEqWithFirstn := 
  match goal with 
    [ H1: List.length ?l1 = List.length ?l2,
      H3: ?l1 ++ ?l1' = ?l2 ++ ?l2' |- ?l1 = ?l2 /\ ?l1' = ?l2' ] =>
    let H := fresh "H" in 
      assert(l1=l2) as H by
        (rewrite <- firstn_length_l with (l:=l1);
          rewrite <- firstn_length_l with (l:=l2);
            rewrite <- firstn_app1 with (l:=l1)(l':=l1'); auto;
              rewrite <- firstn_app1 with (l:=l2)(l':=l2'); auto;
                rewrite H1, H3; trivial);
        rewrite H in H3;
          apply app_inv_head in H3;
            split; assumption
  end.


Lemma decomposeAppCons:
  forall (A:Type)(a b:A)(la la' lb lb':list A),
  la++a::la' = lb++b::lb' ->
  ( List.length la < List.length lb /\
    exists l, ( lb = la ++ a :: l /\ la' = l ++ b :: lb' )) \/
  (la = lb /\ a::la' = b::lb') \/
  ( List.length lb < List.length la /\
    exists l, ( la = lb ++ b :: l /\ lb' = l ++ a :: la' )).
Proof.
  intros A a b la la' lb lb' H.
  destruct(lt_eq_lt_dec (List.length la) (List.length lb)) as [Hleq | Hgt]; 
    try destruct Hleq as [Hlt | Heq]; [ left | right; left | right; right].
  (* Case length la < length lb *)
  Ltac solve a la la' b lb lb' Hlt H := 
    pose(Hlb:=cutInThree lb Hlt a);
      assert(firstn(length la) lb = la) as Hla by
        (set(n:=length la); rewrite <- firstn_length_l with (l:=la); unfold n;
          (rewrite <- firstn_app1 with (l':=b::lb'); try omega);
          (rewrite <- firstn_app1 with (l:=la)(l':=a::la'); trivial); rewrite H; trivial);
        pose(Ha := firstnNth lb (b::lb') la la' a Hlt H a);
          split;auto; rewrite <-Hla, <- Ha; exists (skipn (S(length la)) lb); split;
            try assumption;
              rewrite <- skipn_app1; try omega; rewrite <- H;
                rewrite app_cons; rewrite app_assoc; rewrite skipn_app1; 
                  try (autorewrite with length; simpl; omega);
                    replace (S(length la)) with (length (la++a::nil));
                      [ rewrite skipn_length_l; trivial |
                        autorewrite with length; simpl; omega ].
  solve a la la' b lb lb' Hlt H.
  (* Case length la = lenth lb *)
  listsEqWithFirstn.
  (* Case length lb < length la *)
  symmetry in H; solve b lb lb' a la la' Hgt H.
Qed.

(* this lemma causes a circular dependency with firstn_skipn *)
 Lemma app_length_eq (A: Type) : 
  forall l1 l2 l1' l2' : list A, length l1 = length l1' -> l1++l2 = l1'++l2' -> l1=l1'/\ l2=l2'.
Proof.
  intros  A l1 l2 l1' l2' lenEq appEq.
  split.
  replace l1 with (firstn (length l1) (l1++l2)).
  replace l1' with (firstn (length l1) (l1'++l2')).
  rewrite appEq.
  reflexivity.
  rewrite lenEq.
  
  rewrite  firstn_app_length; reflexivity.
  rewrite  firstn_app_length; reflexivity.
  replace l2 with (skipn (length l1) (l1++l2)).
  replace l2' with (skipn (length l1) (l1'++l2')).
  rewrite appEq.
  reflexivity.
  rewrite lenEq.
  rewrite  skipn_app_length; reflexivity.
  rewrite  skipn_app_length; reflexivity.
Qed.
Hint Resolve app_length_eq :app.
Hint Rewrite  firstn_skipn_length firstn_length_l : length.

 *)

Close Scope N_scope.
