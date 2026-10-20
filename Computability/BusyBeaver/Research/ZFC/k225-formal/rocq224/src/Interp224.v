(** * Interp224: [lprov224] in the 224's code calculus, and the interpreted pure logic.

    [lprov224_thm]: every theorem of [lprov224] has a theorem code in [thm224] (as K230's
    [lprov_thm] for [thm230]); its two vacuity axioms are projections of the 224 bundle.
    [lprov_thm224]: hence every pure-logic theorem of [lprov] has an interpreted code in [thm224].
    [kcore_thm224]: the K core [kcore a b c c] follows from an enabled 224 bundle, through the
    fused core by double-negation cancellation. *)
From Stdlib Require Import Arith Lia List.
From ZF Require Import Logic L1_LDef.
From K230S Require Import KCode230.
From K230L Require Import Codes230.
From K230L Require Comp_Prop230.
From K224 Require Import Codes224 Thm224 CD224 Prop224 L224Def L224E.
Import ListNotations.
Unset Implicit Arguments.

Lemma thm_B3 a b : thm224 (wim a (wim (wim a 1) b)).
Proof.
  apply der_thm. do 2 apply ded.
  apply (dmp _ 1); [apply dthm, thm_F|]. apply (dmp _ a); hyp.
Qed.

(** ** Projections of the fused bundle [-. (Kf -> (V -> -. H))] *)
Lemma dne224 p : thm224 (wim (wim p 1) 1) -> thm224 p.
Proof. intro H. exact (U_mp _ _ H (thm_DNE p)). Qed.

Lemma bundle224_proj a b c : thm224 (bundle224 a b c) ->
  thm224 (kf224 a b c) /\ thm224 (vrel a b c) /\ thm224 (helper224 a b).
Proof.
  intro B. unfold bundle224, wn, F in B.
  set (K := kf224 a b c) in *. set (V := vrel a b c) in *. set (H := helper224 a b) in *.
  repeat split; apply dne224, der_thm, ded; apply (dmp _ (wim K (wim V (wim H 1)))); try (apply dthm, B).
  - apply ded. apply (dmp _ 1); [apply dthm, thm_F|]. apply (dmp _ K); hyp.
  - do 2 apply ded. apply (dmp _ 1); [apply dthm, thm_F|]. apply (dmp _ V); hyp.
  - do 2 apply ded. hyp.
Qed.

Lemma vrel_thm224 x y z : x <> z -> y <> z -> thm224 (wim (wel x y) (wal z (wel x y))).
Proof.
  intros H1 H2. exact (proj1 (proj2 (bundle224_proj _ _ _ (U_bundle x y z (not_eq_sym H1) (not_eq_sym H2))))).
Qed.

Lemma helper_thm224 x y : thm224 (helper224 x y).
Proof.
  assert (H1 : S (x + y) <> x) by lia. assert (H2 : S (x + y) <> y) by lia.
  exact (proj2 (proj2 (bundle224_proj _ _ _ (U_bundle x y (S (x + y)) H1 H2)))).
Qed.

Theorem lprov224_thm a : lprov224 a -> thm224 (tau a).
Proof.
  induction 1 as [a b _ IH1 _ IH2 | x a _ IH | a b c | a | a b | x a b | x y z Hxz Hyz | x y
                  | x y a | x a | x y | x y z | x y z | x y z]; cbn [Comp_Prop230.tau].
  - exact (U_mp _ _ IH2 IH1).
  - now apply U_gen.
  - apply thm_B.
  - apply thm_P.
  - apply thm_B3.
  - apply U_r2.
  - now apply vrel_thm224.
  - apply helper_thm224.
  - apply U_r4.
  - apply (U_r6 x (tau a)).
  - apply (U_r1 x y).
  - apply (U_r7 y z x).
  - apply (U_r5 y z x).
  - apply (U_r3 x y z).
Qed.

Theorem lprov_thm224 a : lprov a -> thm224 (tau (th a)).
Proof. intro H. exact (lprov224_thm _ (lprov_th _ H)). Qed.

(** ** The fused K core, inside [thm224] *)
Definition eqv4 (a b : nat) : Prop := thm224 (wim a b) /\ thm224 (wim b a).

Lemma eqv4_refl a : eqv4 a a.
Proof. split; apply thm_I. Qed.

Lemma dni4 a : thm224 (wim a (wim (wim a 1) 1)).
Proof. apply der_thm. do 2 apply ded. apply (dmp _ a); hyp. Qed.

Lemma eqv4_trans a b c : eqv4 a b -> eqv4 b c -> eqv4 a c.
Proof.
  intros [H1 H2] [H3 H4]. split; apply der_thm, ded.
  - apply (dmp _ b); [apply dthm, H3|]. apply (dmp _ a); [apply dthm, H1|hyp].
  - apply (dmp _ b); [apply dthm, H2|]. apply (dmp _ c); [apply dthm, H4|hyp].
Qed.

Lemma eqv4_dn_l a b : eqv4 a b -> eqv4 (wim (wim a F) F) b.
Proof. intros H. apply (eqv4_trans _ a); [|exact H]. split; [apply thm_DNE|apply dni4]. Qed.

Lemma eqv4_dn_r a b : eqv4 a b -> eqv4 a (wim (wim b F) F).
Proof. intros H. apply (eqv4_trans _ b); [exact H|]. split; [apply dni4|apply thm_DNE]. Qed.

Lemma eqv4_wim a a' b b' : eqv4 a a' -> eqv4 b b' -> eqv4 (wim a b) (wim a' b').
Proof.
  intros [Ha1 Ha2] [Hb1 Hb2]. split; apply der_thm; do 2 apply ded.
  - apply (dmp _ b); [apply dthm, Hb1|]. apply (dmp _ a); [hyp|].
    apply (dmp _ a'); [apply dthm, Ha2|hyp].
  - apply (dmp _ b'); [apply dthm, Hb2|]. apply (dmp _ a'); [hyp|].
    apply (dmp _ a); [apply dthm, Ha1|hyp].
Qed.

Lemma eqv4_wal x a b : eqv4 a b -> eqv4 (wal x a) (wal x b).
Proof.
  intros [H1 H2]. split; [exact (U_mp _ _ (U_gen x _ H1) (U_r2 x a b))
                         |exact (U_mp _ _ (U_gen x _ H2) (U_r2 x b a))].
Qed.

Local Opaque KCode230.P KCode230.wim KCode230.wal KCode230.wel KCode230.weq.

Ltac eqv4_solve :=
  first
  [ apply eqv4_refl
  | apply eqv4_dn_l; eqv4_solve
  | apply eqv4_dn_r; eqv4_solve
  | apply eqv4_wim; eqv4_solve
  | apply eqv4_wal; eqv4_solve ].

Lemma kcore_kf224_4 a b c : eqv4 (kcore a b c c) (kf224 a b c).
Proof. unfold kcore, ksubset, krequest, kf224, wa, wex, wn. eqv4_solve. Qed.

Theorem kcore_thm224 a b c : c <> a -> c <> b -> thm224 (kcore a b c c).
Proof.
  intros Ha Hb. pose proof (proj1 (bundle224_proj _ _ _ (U_bundle a b c Ha Hb))) as HK.
  exact (U_mp _ _ HK (proj2 (kcore_kf224_4 a b c))).
Qed.

Print Assumptions lprov_thm224.
Print Assumptions kcore_thm224.
