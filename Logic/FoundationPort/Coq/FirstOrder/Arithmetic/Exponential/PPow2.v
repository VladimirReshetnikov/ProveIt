(** Iterated powers of two in the standard natural model.

    Foundation's [PPow2 p] holds exactly when [p = 2^(2^k)] for some [k].
    Its internal definition encodes the square chain into a bounded bitset so
    that the predicate is Delta-zero in weak nonstandard arithmetic.  For the
    standard model, an explicit exponent is both simpler and stronger: it is
    executable data and gives uniqueness for free.

    This module ports the central mathematical surface—the square recursion,
    lower bounds, discrete square gaps, and interval uniqueness—without
    postulating the source's internal coding or definability infrastructure. *)

From Stdlib Require Import Lia NArith.NArith.
From Foundation.FirstOrder.Arithmetic.Exponential Require Import Pow2.

Open Scope N_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Definition nat_ppow2 (p : N) : Prop :=
  exists k : N, p = 2 ^ (2 ^ k).

Lemma nat_ppow2_iff_index : forall p,
  nat_ppow2 p <-> exists k, p = 2 ^ (2 ^ k).
Proof. reflexivity. Qed.

Lemma nat_ppow2_power : forall k,
  nat_ppow2 (2 ^ (2 ^ k)).
Proof. intros k. now exists k. Qed.

Lemma nat_ppow2_index_unique : forall p k l,
  p = 2 ^ (2 ^ k) ->
  p = 2 ^ (2 ^ l) ->
  k = l.
Proof.
  intros p k l Hk Hl.
  apply (N.pow_inj_r 2 k l eq_refl).
  apply (N.pow_inj_r 2 (2 ^ k) (2 ^ l) eq_refl).
  congruence.
Qed.

Lemma nat_ppow2_pow2 : forall p,
  nat_ppow2 p -> nat_pow2 p.
Proof.
  intros p [k ->]. exists (2 ^ k). reflexivity.
Qed.

Lemma nat_ppow2_pos : forall p,
  nat_ppow2 p -> 0 < p.
Proof. intros p Hp. exact (nat_pow2_pos (nat_ppow2_pow2 Hp)). Qed.

Lemma nat_ppow2_one_lt : forall p,
  nat_ppow2 p -> 1 < p.
Proof.
  intros p [k ->]. apply N.pow_gt_1; [reflexivity |].
  apply N.pow_nonzero. discriminate.
Qed.

Lemma nat_ppow2_two : nat_ppow2 2.
Proof. exists 0. reflexivity. Qed.

Lemma nat_ppow2_four : nat_ppow2 4.
Proof. exists 1. reflexivity. Qed.

Lemma nat_ppow2_not_zero : ~ nat_ppow2 0.
Proof.
  intro H. exact (N.lt_irrefl 0 (nat_ppow2_pos H)).
Qed.

Lemma nat_ppow2_not_one : ~ nat_ppow2 1.
Proof.
  intro H. exact (N.lt_irrefl 1 (nat_ppow2_one_lt H)).
Qed.

Lemma nat_ppow2_not_three : ~ nat_ppow2 3.
Proof. intro H. exact (nat_pow2_not_three (nat_ppow2_pow2 H)). Qed.

(** Squaring advances the unique iterated exponent index. *)
Lemma nat_ppow2_square_index : forall k,
  (2 ^ (2 ^ k)) * (2 ^ (2 ^ k)) =
  2 ^ (2 ^ N.succ k).
Proof.
  intro k. rewrite <- N.pow_add_r. f_equal.
  rewrite N.pow_succ_r'. lia.
Qed.

Lemma nat_ppow2_square : forall p,
  nat_ppow2 p -> nat_ppow2 (p * p).
Proof.
  intros p [k ->]. exists (N.succ k).
  apply nat_ppow2_square_index.
Qed.

(** Structural recursion corresponding to Foundation's [PPow2.elim]. *)
Lemma nat_ppow2_elim : forall p,
  nat_ppow2 p <->
  p = 2 \/ exists q, p = q * q /\ nat_ppow2 q.
Proof.
  intro p. split.
  - intros [k Hk].
    destruct (N.eq_dec k 0) as [-> | Hnz].
    + now left.
    + right. exists (2 ^ (2 ^ N.pred k)). split.
      * rewrite Hk, <- (N.succ_pred k Hnz) at 1.
        symmetry. apply nat_ppow2_square_index.
      * apply nat_ppow2_power.
  - intros [-> | [q [-> Hq]]].
    + exact nat_ppow2_two.
    + exact (nat_ppow2_square Hq).
Qed.

Lemma nat_ppow2_two_le : forall p,
  nat_ppow2 p -> 2 <= p.
Proof.
  intros p Hp. pose proof (nat_ppow2_one_lt Hp). lia.
Qed.

Lemma nat_ppow2_two_lt : forall p,
  nat_ppow2 p -> p <> 2 -> 2 < p.
Proof.
  intros p Hp Hne.
  destruct (proj1 (nat_ppow2_elim p) Hp) as [H | [q [H Hq]]].
  - contradiction.
  - rewrite H. pose proof (nat_ppow2_two_le Hq). nia.
Qed.

Lemma nat_ppow2_four_le : forall p,
  nat_ppow2 p -> p <> 2 -> 4 <= p.
Proof.
  intros p Hp Hne.
  pose proof (nat_ppow2_two_lt Hp Hne).
  assert (p <> 3) by (intro E; subst p; exact (nat_ppow2_not_three Hp)).
  lia.
Qed.

Lemma nat_ppow2_four_lt : forall p,
  nat_ppow2 p -> p <> 2 -> p <> 4 -> 4 < p.
Proof.
  intros p Hp Hne2 Hne4.
  pose proof (nat_ppow2_four_le Hp Hne2). lia.
Qed.

Lemma nat_ppow2_square_ne_two : forall p,
  nat_ppow2 p -> p * p <> 2.
Proof.
  intros p Hp E.
  pose proof (nat_ppow2_two_le Hp). nia.
Qed.

Lemma nat_ppow2_square_ne_four : forall p,
  nat_ppow2 p -> p <> 2 -> p * p <> 4.
Proof.
  intros p Hp Hne E.
  pose proof (nat_ppow2_two_lt Hp Hne). nia.
Qed.

(** Consecutive iterated powers are at least a square apart. *)
Lemma nat_ppow2_square_le_of_lt : forall p q,
  nat_ppow2 p -> nat_ppow2 q ->
  p < q -> p * p <= q.
Proof.
  intros p q [k ->] [l ->] Hlt.
  assert (Hexp : 2 ^ k < 2 ^ l).
  { exact (proj2 (N.pow_lt_mono_r_iff 2 (2 ^ k) (2 ^ l) eq_refl)
      Hlt). }
  assert (Hdouble : 2 * 2 ^ k <= 2 ^ l).
  { apply (proj1 (@nat_pow2_lt_iff_double_le
      (2 ^ k) (2 ^ l) (nat_pow2_power k) (nat_pow2_power l))).
    exact Hexp. }
  rewrite <- N.pow_add_r.
  apply (proj1 (N.pow_le_mono_r_iff
    2 (2 ^ k + 2 ^ k) (2 ^ l) eq_refl)).
  lia.
Qed.

(** At most one iterated power lies in the interval [(y, y^2)].  The source
    assumes [Pow2 y]; the standard proof does not consume that hypothesis. *)
Lemma nat_ppow2_square_interval_unique : forall y p q,
  nat_ppow2 p -> nat_ppow2 q ->
  y < p -> p <= y * y ->
  y < q -> q <= y * y ->
  p = q.
Proof.
  intros y p q Hp Hq Hyp Hpy Hyq Hqy.
  destruct (N.lt_trichotomy p q) as [Hpq | [-> | Hqp]]; [|reflexivity |].
  - pose proof (nat_ppow2_square_le_of_lt Hp Hq Hpq) as Hsq.
    assert (Hyypp : y * y < p * p).
    { rewrite <- !N.pow_2_r.
      apply N.pow_lt_mono_l; [discriminate | exact Hyp]. }
    lia.
  - pose proof (nat_ppow2_square_le_of_lt Hq Hp Hqp) as Hsq.
    assert (Hyyqq : y * y < q * q).
    { rewrite <- !N.pow_2_r.
      apply N.pow_lt_mono_l; [discriminate | exact Hyq]. }
    lia.
Qed.

(** The wider source interval [(y, 2*y^2)] is also unique when [y] is a
    power of two.  This is the only point where that hypothesis is needed. *)
Lemma nat_ppow2_double_square_interval_unique : forall y p q,
  nat_pow2 y -> nat_ppow2 p -> nat_ppow2 q ->
  y < p -> p <= 2 * (y * y) ->
  y < q -> q <= 2 * (y * y) ->
  p = q.
Proof.
  intros y p q Hy Hp Hq Hyp Hpy Hyq Hqy.
  assert (Hypos : 0 < y) by exact (nat_pow2_pos Hy).
  destruct (N.lt_trichotomy p q) as [Hpq | [-> | Hqp]]; [|reflexivity |].
  - pose proof (nat_ppow2_square_le_of_lt Hp Hq Hpq) as Hpsq.
    assert (Hupper : 2 * (y * y) < (2 * y) * (2 * y)).
    { replace (2 * (y * y)) with ((2 * y) * y) by nia.
      apply (proj1 (N.mul_lt_mono_pos_l (2 * y) y (2 * y)
        ltac:(nia))). lia. }
    assert (Hpsquare : p * p < (2 * y) * (2 * y)) by lia.
    assert (Hplt : p < 2 * y).
    { apply N.nle_gt. intro Hle.
      pose proof (N.mul_le_mono _ _ _ _ Hle Hle). lia. }
    pose proof (proj2 (@nat_pow2_le_iff_lt_double
      p y (nat_ppow2_pow2 Hp) Hy) Hplt).
    lia.
  - pose proof (nat_ppow2_square_le_of_lt Hq Hp Hqp) as Hqsq.
    assert (Hupper : 2 * (y * y) < (2 * y) * (2 * y)).
    { replace (2 * (y * y)) with ((2 * y) * y) by nia.
      apply (proj1 (N.mul_lt_mono_pos_l (2 * y) y (2 * y)
        ltac:(nia))). lia. }
    assert (Hqsquare : q * q < (2 * y) * (2 * y)) by lia.
    assert (Hqlt : q < 2 * y).
    { apply N.nle_gt. intro Hle.
      pose proof (N.mul_le_mono _ _ _ _ Hle Hle). lia. }
    pose proof (proj2 (@nat_pow2_le_iff_lt_double
      q y (nat_ppow2_pow2 Hq) Hy) Hqlt).
    lia.
Qed.

Print Assumptions nat_ppow2_elim.
Print Assumptions nat_ppow2_square_le_of_lt.
Print Assumptions nat_ppow2_square_interval_unique.
Print Assumptions nat_ppow2_double_square_interval_unique.
