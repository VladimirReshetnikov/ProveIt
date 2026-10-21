(** Copy of rocq224/src/Interp222.v (SHA256 17f0b8c0753cc7a4b6c56750a93a001cb3190e9e1e193b2986d75a8a9354678e) under namespace K217F. *)
(** * Interp222: [lprov224] in the seed-K 222's calculus, and the interpreted pure logic.

    As [Interp224] for [thm224]: every [lprov224] theorem has a theorem code in [thm222]. The
    membership vacuity is a projection of the 222 bundle; the equality helper and rho7 are
    derived from the merged row G ([G222]). Composed with the equality interpretation
    [L224E.lprov_th], every theorem of Jeff's [lprov] has an interpreted code in [thm222]. *)
From Stdlib Require Import Arith Lia List.
From ZF Require Import Logic L1_LDef.
From K230S Require Import KCode230.
From K230L Require Import Codes230.
From K230L Require Comp_Prop230.
From K217F Require Import Codes222 Thm222 CD222 Prop222 G222 L224Def L224E.
Import ListNotations.
Unset Implicit Arguments.

Lemma thm_B3 a b : thm222 (wim a (wim (wim a 1) b)).
Proof.
  apply der_thm. do 2 apply ded.
  apply (dmp _ 1); [apply dthm, thm_F|]. apply (dmp _ a); hyp.
Qed.

Lemma dne222 p : thm222 (wim (wim p 1) 1) -> thm222 p.
Proof. intro H. exact (W_mp _ _ H (thm_DNE p)). Qed.

(** Projections of the bundle [-. (RV -> NK)]. *)
Lemma bundle222_proj a b c : thm222 (bundle222 a b c) ->
  thm222 (vrel a b c) /\ thm222 (wim (nks222 a b c) 1).
Proof.
  intro B. unfold bundle222, wn, F in B.
  set (V := vrel a b c) in *. set (K := nks222 a b c) in *.
  split; apply dne222, der_thm, ded; apply (dmp _ (wim V K)); try (apply dthm, B).
  - apply ded. apply (dmp _ 1); [apply dthm, thm_F|]. apply (dmp _ V); hyp.
  - apply ded. apply (dmp _ (wim (wim K 1) 1)); [apply dthm, thm_DNE | hyp].
Qed.

Lemma vrel_thm222 x y z : x <> z -> y <> z -> thm222 (wim (wel x y) (wal z (wel x y))).
Proof.
  intros H1 H2. exact (proj1 (bundle222_proj _ _ _ (W_bundle x y z (not_eq_sym H1) (not_eq_sym H2)))).
Qed.

Theorem lprov224_thm222 a : lprov224 a -> thm222 (tau a).
Proof.
  induction 1 as [a b _ IH1 _ IH2 | x a _ IH | a b c | a | a b | x a b | x y z Hxz Hyz | x y
                  | x y a | x a | x y | x y z | x y z | x y z]; cbn [Comp_Prop230.tau].
  - exact (W_mp _ _ IH2 IH1).
  - now apply W_gen.
  - apply thm_B.
  - apply thm_P.
  - apply thm_B3.
  - apply W_r2.
  - now apply vrel_thm222.
  - apply helper222.
  - apply W_r4.
  - apply (W_r6 x (tau a)).
  - apply (W_r1 x y).
  - apply (rho7_222 y z x).
  - apply (W_r5 y z x).
  - apply (W_r3 x y z).
Qed.

Theorem lprov_thm222 a : lprov a -> thm222 (tau (th a)).
Proof. intro H. exact (lprov224_thm222 _ (lprov_th _ H)). Qed.

Print Assumptions lprov_thm222.
