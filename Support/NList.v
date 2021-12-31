Require Import SyDPaCC.Support.Sig SyDPaCC.Support.List.
Require Import Coq.Lists.List Arith NArith NPeano Lia Recdef.
Import ListNotations.

Set Implicit Arguments.
Generalizable All Variables.
Open Scope N_scope.


(** * List Functions using Binary Natural Numbers *)

(** ** List length that returns a [N] *)

(** A length function that returns a value of type [N]. *)
Fixpoint length (A:Type)(l:list A) : N := 
  match l with 
    | [] => 0 
    | h::t => N.succ (length t)
  end.

Fact length_cons:
  forall A (x:A) xs,
    length(x::xs) = 1 + length xs.
  intros.
  simpl(length(x::xs)).
  now rewrite N.add_1_l.
Qed.

#[export] Hint Resolve length_cons : length.

Fact length_nil:
  forall A (x:A) xs,
    not (@length A []  = length(x::xs)).
  intros. intro H.
  rewrite length_cons in H.
  simpl in H.
  destruct (length xs); lia.
Qed.

#[export] Hint Rewrite length_cons : length.

#[export] Hint Rewrite <- N.add_1_l : length.

(** [List.length] returns the same value than [length], up to
    conversion from [nat] to [N]. *)
Lemma length_Nlength:
  forall (A:Type)(l:list A),
    List.length l = nat_of_N (length l).
Proof.
  intros A; induction l as [ | x xs IH ].
  - trivial.
  - replace(length(x::xs)) with (1+length xs) by auto with length.
    rewrite N2Nat.inj_add.
    simpl; auto using IH.
Qed.

(** [length] returns the same value than [List.length], up to
    conversion from [N] to [nat]. *)
Lemma Nlength_length:
  forall (A:Type)(l:list A),
    length l = N_of_nat (List.length l).
Proof.
  intros A; induction l as [ | x xs IH ].
  - trivial.
  - replace(List.length(x::xs)) with(S(List.length xs)) by auto with length.
    rewrite Nat2N.inj_succ.
    simpl; now rewrite <- IH, <- N.add_1_l.
Qed.

Lemma map_length:
  forall {A B} (f:A->B) l,
    length(map f l) = length l.
Proof.
  intros A B f l.
  repeat rewrite Nlength_length; f_equal.
  apply List.map_length.
Qed.

Lemma app_length:
  forall {A} (l1 l2:list A),
    length(l1 ++ l2) = length l1 + length l2.
Proof.
  intros A l1 l2.
  repeat rewrite Nlength_length.
  rewrite List.app_length.
  lia.
Qed.

#[export] Hint Rewrite @map_length @app_length : length.

Lemma combine_length:
  forall (A B:Type) (l1: list A)(l2: list B),
    length(combine l1 l2) = N.min (length l1) (length l2).
Proof.
  intros A B l1 l2.
  repeat rewrite Nlength_length in *; f_equal.
  autorewrite with length.
  lia.
Qed.

#[export] Hint Rewrite combine_length : length.

Lemma combine_length':
    forall {A B: Type}{l:list A}{l':list B}(H:length l=length l'),
      length(combine l l') = length l.
Proof.
  intros; rewrite combine_length; lia.
Qed.

Lemma combine_length'':
  forall {A B: Type}{l:list A}{l':list B}(H:length l=length l'),
    length(combine l l') = length l'.
Proof.
  intros; rewrite combine_length; lia.
Qed.

#[export] Hint Rewrite @combine_length' @combine_length'' : length.

(** ** Creation of sequences of natural numbers of type [N]. *)

(** [seq] takes number of type [N] and returns a list of numbers of type [N]. *)
Function seq (first:N)(size:N) { wf N.lt size } : list N := 
  match size with 
    | 0 => [] 
    | N => first::(seq (N.succ first) (N.pred size))
  end.
Proof.
  intros first size p teq; subst; apply N.lt_pred_l; lia.
  apply N.lt_wf_0.
Qed.

Lemma seq_S_app:
  forall (first size :N),
    seq first (N.succ size) = ( seq first size ) ++ [ first + size ].
Proof.
  intros first size; generalize dependent first; 
  induction size using N.peano_ind; intro first.
  + do 3 (rewrite seq_equation; simpl); rewrite N.add_0_r; trivial.
  + rewrite seq_equation; simpl; destruct size; simpl.
    * do 4 (rewrite seq_equation; simpl).
      rewrite N.add_1_r; trivial.
    * rewrite Pos.pred_N_succ, IHsize.
      replace (Npos(Pos.succ p)) with (N.succ (Npos p)); auto.
      rewrite seq_equation with (size:=N.succ (Npos p)); simpl.
      rewrite Pos.pred_N_succ.
      do 3 f_equal. lia.
Qed.

Lemma seq_seq:
  forall (first size :N),
    seq first size = 
        List.map N.of_nat (List.seq (N.to_nat first) (N.to_nat size)).
Proof.
  intros first size; generalize dependent first; 
  induction size using N.peano_ind; intro first; simpl.
  + apply seq_equation.
  + rewrite N2Nat.inj_succ. rewrite seq_S_app; simpl.
    replace(S(N.to_nat first)) with (N.to_nat(N.succ first))
      by now rewrite <- N2Nat.inj_succ.
    rewrite <- IHsize. 
    rewrite seq_equation; destruct size; simpl.
    * rewrite seq_equation; f_equal; lia.
    * rewrite N2Nat.id; f_equal.
      replace (first+N.pos p) with (N.succ first + Pos.pred_N p).
      rewrite <- seq_S_app.
      now rewrite N.succ_pos_pred.
      replace (N.succ first) with (1 + first) by (lia).
      rewrite <- N.succ_pos_pred with (p:=p).
      lia.
Qed.

Lemma seq_length:
  forall (first size: N), 
    length(seq first size) = size.
Proof.
  intros first size; generalize dependent first;
  induction size using N.peano_ind; intro first; rewrite seq_equation.
  - trivial.
  - destruct size. 
    + simpl; rewrite seq_equation; auto with arith.
    + simpl. rewrite Pos.pred_N_succ, IHsize. destruct p; trivial.
Qed.

#[export] Hint Rewrite seq_length : length.

Lemma In_seq len start n :
  In n (seq start len) <-> start <= n < start+len.
Proof.
  rewrite seq_seq; split; intro H.
  - apply in_map_iff in H.
    destruct H as [ m [ H Hin] ].
    rewrite in_seq in Hin.
    lia.
  - apply in_map_iff.
    exists (N.to_nat n).
    split.
    + apply N2Nat.id.
    + apply in_seq; lia.
Qed.

Lemma In_seq_split:
  forall k start len,
    In k (seq start len) ->
    seq start len = seq start (k-start)++k::(seq (N.succ k) ((start+len)-(N.succ k))).
Proof.
  intros k start len; revert k start; 
    induction len as [ | len IH ] using N.peano_ind; intros k start Hin.
  - rewrite seq_equation in *. inversion Hin.
  - rewrite seq_seq, N2Nat.inj_succ, seq_S_len, map_app, in_app_iff, <- seq_seq in Hin.
          destruct Hin as [ Hin | Hin ].
    + assert(N.succ k <= start+len)
        by (apply In_seq in Hin; destruct Hin; lia).
      apply IH in Hin.
      rewrite seq_seq, N2Nat.inj_succ, seq_S_len, map_app, <- seq_seq.
      rewrite Hin; simpl.
      rewrite <- List.app_assoc; f_equal.
      rewrite  <- app_comm_cons; f_equal.
      repeat rewrite seq_seq; f_equal.
      rewrite N.add_succ_r, N.sub_succ_l by auto.
      repeat rewrite N2Nat.inj_succ.
      rewrite seq_S_len; repeat rewrite map_app.
      rewrite <- N2Nat.inj_succ. simpl; do 2 f_equal.
      repeat rewrite Nat2N.inj_add, N2Nat.id.
      repeat rewrite N2Nat.id.
      lia.
    + simpl in Hin; destruct Hin as [ Hin | Hin ]; try now exfalso.
      rewrite Nat2N.inj_add, N2Nat.id, N2Nat.id in Hin.
      rewrite <- Hin in *; clear Hin.
      rewrite N.add_comm with (n:=start), N.add_sub.
      rewrite N.add_comm, N.add_succ_r, N.sub_diag.
      rewrite seq_equation with (size:=0).
      rewrite seq_seq, N2Nat.inj_succ, seq_S_len, map_app, <- seq_seq; f_equal.
      simpl; rewrite Nat2N.inj_add. now repeat rewrite N2Nat.id.
Qed.

(** ** An [nth] function that takes arguments of type [N] *)

Function nth (A:Type) (pos:N) (l:list A) (default:A) : A :=
  match l with
  | [ ]  => default
  | a::l => match pos with
           | 0 => a
           | _ => nth (N.pred pos) l default
           end
  end.

Lemma  nth_seq:
  forall A l (d:A),
    l = List.map (fun i => nth i l d) (seq 0 (length l)).
Proof.
  intro A; induction l as [ | h t IH]; intro d.
  - now rewrite seq_equation.
  - rewrite seq_equation.
    replace(match length(h::t) with | 0 => _ | _ => _ end) with
    (0 :: seq 1 (length t)).
    + simpl; rewrite IH with (d:=d); f_equal.
      repeat rewrite seq_seq, map_map.
      rewrite <- length_Nlength, Nlength_length.
      autorewrite with length.
      rewrite Nnat.Nat2N.id; simpl.
      replace (Pos.to_nat 1) with (1%nat) by now compute.
      rewrite <- seq_shift, map_map.
      apply map_ext_in.
      intros a Hin.
      rewrite Nnat.Nat2N.inj_succ, <- N.succ_pos_spec, N.succ_pos_spec, N.pred_succ.
      rewrite IH with (d:=d) at 1.
      f_equal. rewrite seq_seq, map_map, <- length_Nlength.
      trivial.
    + replace (N.pred (length(h::t))) with (length t)
        by now rewrite length_cons, N.add_1_l, N.pred_succ.
      simpl; now rewrite <- N.succ_pos_spec.
Qed.   

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
      apply IH; auto; lia.
Qed.
    
Module Sig.

  (** A strong version of [nth]. *)
  
  Program Fixpoint nth {A:Type} (l:list A) (pos:N | pos < length l) : A := 
    match l with 
      | [] => _
      | a::l => 
        if N.eq_dec (proj1_sig pos) 0 
        then a 
        else nth l (N.pred (proj1_sig pos))
    end.
  Next Obligation. simpl in *; lia. Qed.
  Next Obligation.
    match goal with
      [ HH: _ < length(a::l) |- _ ] =>
        replace (length(a::l)) with (1 + length l) in HH  by auto with length
    end.
    assert(N.pred pos < pos) by now apply N.lt_pred_l.
    lia.
  Qed.

  Lemma nth_spec : 
    forall (A:Type) (l:list A)  (pos:N | pos<length l) (default : A), 
      nth l pos = List.nth (N.to_nat (proj1_sig pos)) l default.
  Proof.
    induction l; intros [pos Hpos] default.
    - contradict Hpos; simpl; lia.
    - destruct pos using N.peano_ind; trivial.
      simpl; rewrite Nnat.N2Nat.inj_succ.
      destruct(N.eq_dec (N.succ pos) 0) as [ Hl | Hr ].
      + contradict Hl; lia.
      + rewrite IHl with (default:=default); simpl.
        f_equal; now rewrite N.pred_succ.
  Qed.
  
  Lemma nth_pi : 
    forall (A:Type)(l :list A) (pos1 pos2: {n:N | n < length l}),
      proj1_sig pos1 =  proj1_sig pos2 ->
      nth l pos1 = nth l pos2.
  Proof.
    intros A l [pos1 Hpos1] [pos2 Hpos2] H; simpl in H; subst.
    destruct l.
    - simpl in Hpos1; contradict Hpos1; lia.
    - now repeat rewrite nth_spec with (default := a).
  Qed.

  Program Lemma nth_In : 
    forall (A:Type) (l:list A) (pos:N | pos < length l),
      In (nth l pos) l.
  Proof.
    intros A l [pos Hpos]; subst.
    destruct l as [ | x xs].
    - simpl in Hpos; contradict Hpos; lia.
    - rewrite nth_spec with (default:=x).
      assert(length (x::xs) = 1 + length xs) as Heq by auto with length.
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
            by (autorewrite with length; lia).
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
            by (autorewrite with length; lia).
        set(pos0:=exist (fun n=>n<_) 0 H0). 
        now specialize (H pos0). 
      }
      assert(length xs = length xs') as Hlen'.
      {
        clear H. 
        autorewrite with length in Hlen.
        lia.
      }
      assert(forall (pos : N | pos < length xs),
                nth xs pos =
                nth xs' (cast_sig pos (length_sig Hlen'))) as Htail.
      {
        intros [pos Hpos]. 
        assert(N.succ pos<length(x::xs)) as Hpos'
            by (autorewrite with length; lia).
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
    - simpl in pos; destruct pos as [pos H]; contradict H; lia.
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
    induction l as [ | a l IH]; destruct l' as [ | b l'];
      intros [pos Hpos] H;
      try (simpl in Hpos; contradict Hpos; lia).
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
    - simpl in Hpos; contradict Hpos; lia.
    - destruct pos using N.peano_ind.
      + simpl. f_equal. apply UIP0.      
      + assert(exists H, N.eq_dec (N.succ pos) 0 = right H) as Heq.
        {
          clear.
          destruct(N.eq_dec (N.succ pos) 0) as [ Hl | Hr ].
          - contradict Hl; lia.
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

#[export] Hint Rewrite @Sig.map_length : length.

(** **  *)

(** ** [mapi] and variants *)

Fixpoint mapi_aux {A B:Type} (f:N -> A -> B) (l:list A) (i:N): list B := 
  match l with 
    | nil => nil 
    | cons x xs => cons (f i x) (mapi_aux f xs (i+1))
  end.

Definition mapi  {A B:Type} (f:N -> A -> B) (l:list A) : list B := 
  mapi_aux f l 0.

Lemma length_mapi_aux: 
  forall {A B:Type} (f:N -> A -> B)(l:list A)(i:N),
    length(mapi_aux f l i) = length l.
Proof.
  induction l.
  - trivial.
  - simpl. intro i. rewrite IHl. trivial.
Qed.

#[export] Hint Rewrite @length_mapi_aux : length.

Lemma length_mapi: 
  forall {A B:Type} (f:N -> A -> B)(l:list A),
    length(mapi f l) = length l.
Proof.
  unfold mapi. 
  intros.
  apply length_mapi_aux.
Qed.

#[export] Hint Rewrite @length_mapi : length.

Lemma mapi_app:
  forall {A B:Type} (f:N -> A -> B) (l l':list A)(i:N),
    mapi_aux f (l++l') i = 
    (mapi_aux f l i) ++ (mapi_aux f l' 
                                (i+length l)).
Proof.
  induction l; intros l' i.
  - simpl. rewrite Nplus_0_r. trivial.
  - Opaque N.add. simpl. rewrite IHl. rewrite  <- N.add_1_l, N.add_assoc. trivial.
Qed.
    
Lemma mapi_aux_nth:
  forall (A B: Type)(f: N->A->B)(l:list A)(position first:N)(default:A),
  nth position (mapi_aux f l first) (f ((first+position)%N) default) =  
  f ((first+position)%N) (nth position l default).
Proof.
  intros A B f; induction l; intros position first default.
  - destruct position using N.peano_ind.
    + rewrite N.add_0_r. trivial.
    + trivial.
  - destruct position using N.peano_ind.
    + rewrite N.add_0_r. trivial.
    + simpl mapi_aux.
      rewrite nth_equation.
      destruct (N.succ position) eqn:Hpos.
      * apply N.succ_0_discr in Hpos.
        now exfalso.
      * rewrite <- Hpos; rewrite nth_equation with (pos:=N.succ position).
        rewrite Hpos, <- Hpos, N.pred_succ.
        replace (first + N.succ position)%N with ( (first + 1) + position)%N
          by lia.
        now rewrite IHl.
Qed.

Lemma mapi_nth:
  forall (A B: Type)(f: N->A->B)(l:list A)(position:N)(default:A),
  nth position (mapi f l) (f position default) =  
  f position (nth position l default).
Proof.
  unfold mapi.
  intros A B f l position default.
  rewrite mapi_aux_nth.
  trivial.
Qed.

#[export] Hint Rewrite @map_length : length.

(** ** [firstn] and [skipn] function that take arguments of type [N] *)

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
  intros A l n; generalize dependent l;
    induction n as [ | n IH ] using N.peano_ind; intro l; simpl.
  - rewrite skipn_equation; lia.
  - rewrite skipn_equation.
    destruct(N.succ n) eqn:Heq.
    + lia.
    + destruct l as [ | a l ].
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

#[export] Hint Rewrite skipn_length skipn_length_l: length.

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

(** [firstn] applied to [l++l'] is equal to firstn applied to [l] if the length of [l] is greater than n  *)
Lemma firstn_app1:
  forall A (l l':list A) n,
    n <= length l -> firstn n (l++l') = firstn n l.
Proof.
  induction l as [|a l IHl]; intros l' n H.
  - simpl in *; assert(n = 0) by (lia); subst.
    now rewrite firstn_equation.
  - destruct n using N.peano_ind.
    + now repeat rewrite firstn_equation.
    + do 2 rewrite firstn_equation.
      rewrite <- app_comm_cons, N.pred_succ, IHl.
      * reflexivity.
      * rewrite length_cons in H.
        lia.
Qed.

(** [firstn  (length l) l] is [l] *)
Lemma firstn_length:
  forall A (l:list A), firstn (length l) l = l.
Proof.
  induction l; auto; simpl; f_equal.
  now rewrite <- N.succ_pos_spec, N.succ_pos_spec, N.pred_succ, IHl.
Qed.
      
(** [firstn] applied to [l++l'] is equal to  [l] if the length of [l] is  n  *)
Lemma firstn_app_length:
  forall A (l l':list A) n,
    n = length l -> firstn n (l++l') = l.
Proof.
  intros A l l' n length_l.
  rewrite  firstn_app1 by lia; rewrite length_l.
  rewrite firstn_length; auto.
Qed.

(** [skipn] applied to [l++l'] is equal to skipn applied to [l] append
    to [l'] if the length of [l] is greater than [n] *)
Lemma skipn_app1: 
  forall A (l l':list A) n,
    n <= length l -> skipn n (l++l') = (skipn n l) ++ l'.
Proof.
  intros A l; induction l as [ | h t IH]; intros l' n H.
  - destruct n as [ | n ]; rewrite skipn_equation.
    + trivial.
    + simpl in H; lia.
  - destruct n as [ | n ].
    + trivial.
    + rewrite  <- N.succ_pos_pred in H; autorewrite with length in H.
      simpl skipn at 1; now erewrite IH by (lia).
Qed.

(** [skipn] applied to [l++l'] is equal to skip [n - length l] element
    of [l'] if the length of [l] is lesser than [n] *)
Lemma skipn_app2:
  forall A (l l':list A) n,
    n >= length l -> skipn n (l++l') = skipn (n-length l) l'.
Proof.
  intros A l; induction l as [ | h t IH]; intros l' n H.
  - simpl; f_equal; lia.
  - destruct n as [ | n ].
      + simpl in *;lia.
      + autorewrite with length in H; rewrite  <- N.succ_pos_pred in H.
        simpl skipn at 1; rewrite IH by (lia).
        f_equal; autorewrite with length; rewrite <- N.succ_pos_pred.
        lia.
Qed.

(** compositions of [skipn]  *)
Lemma skipn_skipn: 
  forall A (l: list A) n m,
    skipn n (skipn m l) = skipn (n+m) l.
Proof.
  intros A l; induction l as [ | h t IH]; intros n m.
  - destruct n; destruct m; trivial.
  - destruct n; destruct m; trivial.
    + now rewrite skipn_equation.
    + replace (h::t) with ([h]++t) by auto.
      repeat rewrite skipn_app2 by (autorewrite with length; simpl; lia).
      rewrite IH; f_equal; simpl length; lia.
Qed.

Close Scope N_scope.
