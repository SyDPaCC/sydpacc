Require Import Coq.Lists.List Program. Import ListNotations.
Require Import SyDPaCC.Core.Bmf SyDPaCC.Support.List.
Set Implicit Arguments.
Generalizable All Variables.

(*---------------------------------------------------------*)

(** * The Diffusion Theorem for Accumulative Computations  *)

Theorem diffusion:
  forall A B C (h: B -> list A -> C) (g:B->C) (p:A*B->C) (q:A->B)
    (oplus:C->C->C) (otimes:B->B->B) 
    `(Monoid _ oplus e_oplus) 
    `(Monoid _ otimes e_otimes),
    (forall c, h c [] = g c) ->
    (forall c x xs,  h c (x::xs) = oplus (p (x,c)) (h (otimes c (q x)) xs)) ->
    forall xs c,
      let bs := map (otimes c) (scan otimes (map q xs)) in 
      let ys := List.combine xs (removelast bs) in 
      h c xs = oplus ( reduce oplus (map p ys) ) (g (last bs)).
Proof.
  intros A B C h g p q oplus otimes e_oplus Hopluq e_otimes Hotimes H1 H2.
  induction xs as [ | x xs IH]; intros c bs ys.
  - rewrite H1; unfold bs; compute. 
    now rewrite left_neutral, right_neutral.
  - assert(bs = c :: map (otimes (otimes c (q x))) (scan otimes (map q xs))) as Hbs.
    {
      clear; unfold bs; simpl; clear bs.
      rewrite right_neutral. f_equal.
      autounfold with sydpacc; repeat rewrite <- scanl_map.
      f_equal.
      symmetry; rewrite right_neutral.
      f_equal; now rewrite left_neutral.
    }
    assert(last bs = last (map(otimes(otimes c (q x)))(scan otimes (map q xs)))) as Hlast.
    {
      assert(last bs = last (c::map(otimes(otimes c (q x)))(scan otimes (map q xs)))) as H'
          by now apply last_pi.
      rewrite H'.
      apply last_cons_non_empty.
    }
    set(bs' := map (otimes (otimes c (q x))) (scan otimes (map q xs))) in *.
    set(ys' := combine xs (removelast bs')).
    assert(ys = (x,c)::ys') as Hys.
    {
      unfold ys, ys'.
      rewrite Hbs.
      replace (c :: bs') with ([c] ++ bs') by trivial.
      now rewrite removelast_app by (apply non_emptiness; typeclasses eauto).
    }
    rewrite Hys.
    replace (g(last bs)) with (g(last bs'))
      by (f_equal; now rewrite <- Hlast).
    simpl. rewrite reduce_eq.
    rewrite H2.
    rewrite IH.
    now rewrite associative.
Qed.

Theorem diffusion_scanl_last:
  forall A B C (h: B -> list A -> C) (g:B->C) (p:A*B->C) (q:A->B)
    (oplus:C->C->C) (otimes:B->B->B) 
    `(Monoid _ oplus e_oplus) 
    `(Monoid _ otimes e_otimes),
    (forall c, h c [] = g c) ->
    (forall c x xs,  h c (x::xs) = oplus (p (x,c)) (h (otimes c (q x)) xs)) ->
    forall xs c,
      let bsb := scanl_last otimes e_otimes (map q xs) in
      let (bs,b) := (map (otimes c) (fst bsb), otimes c (snd bsb)) in 
      let ys := List.combine xs bs in 
      h c xs = oplus ( reduce oplus (map p ys) ) (g b).
Proof.
  intros A B C h g p q oplus otimes e_oplus Moplus e_otimes Motimes Heq1 Heq2 xs c bsb.
  set(Diff := diffusion h g p q Moplus Motimes Heq1 Heq2).
  rewrite Diff; simpl; unfold bsb; do 2 f_equal.
  - unfold scan; rewrite scanl_scanl_last; simpl.
    rewrite removelast_map, removelast_app by
      (intros; discriminate); simpl.
    now rewrite app_nil_r.
  - rewrite last_map; f_equal.
    unfold scan; erewrite last_pi with (l':=scanl otimes e_otimes (map q xs)) by auto.
    apply last_scanl.
Qed.

(** * The Sequential [accumulate] Function *)

Fixpoint accumulate A B C (g:B->C) (p:A*B->C) (q:A->B)(oplus:C->C->C) (otimes:B->B->B) 
         c l : C :=
  match l with
  | [ ] => g c
  | x::xs => oplus (p (x,c)) (accumulate g p q oplus otimes (otimes c (q x)) xs)
  end.

Open Scope sydpacc_scope.

(** * Diffusion for [accumulate] *)

#[export] Instance diffusion_accumulate
         `(g:B->C) `(p:A*B->C) (q:A->B)
         `{Hp:Monoid C oplus e_oplus} `{Ht:Monoid B otimes e_otimes}
         (c:B) :
  Opt (accumulate g p q oplus otimes c)
      ( (prod_curry oplus)
          ∘ ( ((prod_curry (fold_left2 (fun (u:C) (vw:A*B)=>oplus u (p vw)) e_oplus)) × g )
                ∘ ( ( (id × fst) △ (snd ∘ snd) )
                      ∘ ( id △ (scanl_last (fun s t=>otimes s (q t)) c) ) ) ) ).
Proof.
  constructor; intro xs; autounfold with sydpacc; simpl.
  set(Diff := diffusion_scanl_last (accumulate g p q oplus otimes) g p q Hp Ht); simpl in Diff.
  rewrite Diff by auto; unfold reduce.
  rewrite fold_left2_prop2.
  repeat rewrite scanl_last_fst_scanl.
  rewrite <- removelast_map. 
  rewrite <- @scanl_map with (op:=otimes)(x:=c) by typeclasses eauto.
  repeat rewrite scanl_last_snd. 
  erewrite map_scanl by typeclasses eauto.
  rewrite fold_left_map_r with (g:=q).
  rewrite <- fold_left_prop by typeclasses eauto.
  now repeat rewrite @right_neutral with (op:=otimes) by typeclasses eauto.
Qed.

Close Scope sydpacc_scope.
