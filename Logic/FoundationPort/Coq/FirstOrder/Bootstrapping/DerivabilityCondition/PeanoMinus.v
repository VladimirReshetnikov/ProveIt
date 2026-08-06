(**
  Semantic arithmetic lemmas used by bootstrapped PA-minus.

  The source develops these facts inside an internalized arithmetic proof
  system.  The algebraic content is independent of coding and proof syntax,
  so it is stated for every explicit [peano_minus_laws] carrier.  Existing
  numeral addition, multiplication, and order reflection in
  [Arithmetic.PeanoMinus.Basic] provide the remaining standard-model
  arithmetic API.
*)

From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Source counterpart of [Arithmetic.lt_add_self_add_one]. *)
Lemma peano_minus_boot_lt_add_self_add_one : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  oring_lt O a
    (oring_add O (oring_add O b a) (oring_one O)).
Proof.
  intros M O H a b.
  apply (peano_minus_le_lt_add_one H
    (x := a) (y := oring_add O b a)).
  rewrite (@peano_minus_add_comm M O H b a).
  apply (peano_minus_le_add_right H).
Qed.

(** Source counterpart of [Arithmetic.lt_succ_iff_eq_or_succ]. *)
Lemma peano_minus_boot_lt_succ_iff_eq_or_lt : forall M
    (O : oring_carrier M),
  peano_minus_laws O -> forall a b,
  oring_lt O a (oring_add O b (oring_one O)) <->
  a = b \/ oring_lt O a b.
Proof.
  intros M O H a b. split.
  - intro Hab.
    destruct (proj2 (@peano_minus_le_iff_lt_add_one M O H a b) Hab)
      as [Heq | Hlt].
    + left. exact Heq.
    + right. exact Hlt.
  - intros [-> | Hab].
    + apply (@peano_minus_lt_add_one M O H b).
    + eapply (@peano_minus_lt_trans M O H a b
        (oring_add O b (oring_one O))).
      * exact Hab.
      * apply (@peano_minus_lt_add_one M O H b).
Qed.
