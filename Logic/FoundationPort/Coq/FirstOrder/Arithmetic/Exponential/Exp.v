(** The binary exponential graph in the standard natural model.

    Foundation constructs a bounded sequence certificate so that the graph of
    [2^x] is Delta-zero definable in weak nonstandard arithmetic.  In the
    standard model, the graph is simply equality with Stdlib's executable
    power function.  This presentation checks the mathematical API directly
    and makes totality, functionality, and uniqueness constructive.

    Internal sequence codes and formula-level definability remain outside
    this module; no surrogate graph predicate is postulated. *)

From Stdlib Require Import Lia NArith.NArith.
From Foundation.FirstOrder.Arithmetic.Exponential Require Import Pow2 PPow2.

Open Scope N_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Definition nat_exponential (x y : N) : Prop :=
  y = 2 ^ x.

Definition nat_exp (x : N) : N := 2 ^ x.

Lemma nat_exponential_graph : forall x y,
  nat_exponential x y <-> y = nat_exp x.
Proof. reflexivity. Qed.

Lemma nat_exponential_zero_one : nat_exponential 0 1.
Proof. reflexivity. Qed.

Lemma nat_exponential_one_two : nat_exponential 1 2.
Proof. reflexivity. Qed.

Lemma nat_exponential_two_four : nat_exponential 2 4.
Proof. reflexivity. Qed.

Lemma nat_exponential_range_pow2 : forall x y,
  nat_exponential x y -> nat_pow2 y.
Proof. intros x y ->. apply nat_pow2_power. Qed.

Lemma nat_exponential_range_iff_pow2 : forall y,
  nat_pow2 y <-> exists x, nat_exponential x y.
Proof.
  intro y. split.
  - intros [x Hx]. exists x. exact Hx.
  - intros [x Hx]. exact (nat_exponential_range_pow2 Hx).
Qed.

Lemma nat_exponential_range_pos : forall x y,
  nat_exponential x y -> 0 < y.
Proof. intros x y H. exact (nat_pow2_pos (nat_exponential_range_pow2 H)). Qed.

Lemma nat_exponential_lt : forall x y,
  nat_exponential x y -> x < y.
Proof.
  intros x y ->. apply N.pow_gt_lin_r. reflexivity.
Qed.

Lemma nat_not_exponential_of_le : forall x y,
  x <= y -> ~ nat_exponential y x.
Proof.
  intros x y Hle Hexp.
  pose proof (nat_exponential_lt Hexp). lia.
Qed.

(** Doubling an exponent squares the range. *)
Lemma nat_exponential_even_intro : forall x y,
  nat_exponential x y ->
  nat_exponential (2 * x) (y * y).
Proof.
  intros x y ->. unfold nat_exponential.
  rewrite <- N.pow_add_r. f_equal. lia.
Qed.

Lemma nat_exponential_even : forall x y,
  nat_exponential (2 * x) y <->
  exists y', y = y' * y' /\ nat_exponential x y'.
Proof.
  intros x y. split.
  - intros ->. exists (2 ^ x). split.
    + rewrite <- N.pow_add_r. f_equal. lia.
    + reflexivity.
  - intros [y' [-> Hy]]. exact (nat_exponential_even_intro Hy).
Qed.

Lemma nat_exponential_even_square : forall x y,
  nat_exponential (2 * x) (y * y) <-> nat_exponential x y.
Proof.
  intros x y. split; [|apply nat_exponential_even_intro].
  intro H.
  destruct (proj1 (nat_exponential_even x (y * y)) H)
    as [z [Hz Hzexp]].
  pose proof (f_equal N.sqrt Hz) as E.
  rewrite !N.sqrt_square in E.
  unfold nat_exponential in Hzexp |- *.
  now rewrite E, Hzexp.
Qed.

(** An odd exponent contributes one additional factor of two. *)
Lemma nat_exponential_odd_intro : forall x y,
  nat_exponential x y ->
  nat_exponential (2 * x + 1) (2 * (y * y)).
Proof.
  intros x y ->. unfold nat_exponential.
  rewrite <- N.pow_add_r.
  rewrite <- N.pow_succ_r'. f_equal. lia.
Qed.

Lemma nat_exponential_odd : forall x y,
  nat_exponential (2 * x + 1) y <->
  exists y', y = 2 * (y' * y') /\ nat_exponential x y'.
Proof.
  intros x y. split.
  - intros ->. exists (2 ^ x). split.
    + rewrite <- N.pow_add_r, <- N.pow_succ_r'. f_equal. lia.
    + reflexivity.
  - intros [y' [-> Hy]]. exact (nat_exponential_odd_intro Hy).
Qed.

Lemma nat_exponential_succ : forall x y,
  nat_exponential (x + 1) y <->
  exists z, y = 2 * z /\ nat_exponential x z.
Proof.
  intros x y. split.
  - intros ->. exists (2 ^ x). split; [|reflexivity].
    replace (x + 1) with (N.succ x) by lia.
    apply N.pow_succ_r'.
  - intros [z [-> Hz]]. unfold nat_exponential in Hz |- *.
    rewrite Hz. replace (x + 1) with (N.succ x) by lia.
    symmetry. apply N.pow_succ_r'.
Qed.

Lemma nat_exponential_succ_double : forall x y,
  nat_exponential (x + 1) (2 * y) <-> nat_exponential x y.
Proof.
  intros x y. split.
  - intro H. destruct (proj1 (nat_exponential_succ x (2 * y)) H)
      as [z [Hz He]].
    assert (y = z).
    { apply (proj1 (N.mul_cancel_l y z 2 ltac:(discriminate))).
      exact Hz. }
    now subst z.
  - intro H. apply (proj2 (nat_exponential_succ x (2 * y))).
    now exists y.
Qed.

Lemma nat_exponential_elim : forall x y,
  nat_exponential x y <->
  (x = 0 /\ y = 1) \/
  exists x' y',
    x = x' + 1 /\ y = 2 * y' /\ nat_exponential x' y'.
Proof.
  intros x y. split.
  - intro H. destruct (N.eq_dec x 0) as [-> | Hnz].
    + left. split; [reflexivity | exact H].
    + right. exists (N.pred x), (2 ^ N.pred x). split.
      * pose proof (N.succ_pred x Hnz). lia.
      * split.
        -- unfold nat_exponential in H. rewrite H.
           rewrite <- (N.succ_pred x Hnz) at 1.
           apply N.pow_succ_r'.
        -- reflexivity.
  - intros [[-> ->] | [x' [y' [-> [-> H]]]]].
    + exact nat_exponential_zero_one.
    + exact (proj2 (nat_exponential_succ_double x' y') H).
Qed.

Lemma nat_exponential_zero_unique : forall y,
  nat_exponential 0 y <-> y = 1.
Proof. intro y. unfold nat_exponential. simpl. tauto. Qed.

Lemma nat_exponential_functional : forall x y z,
  nat_exponential x y -> nat_exponential x z -> y = z.
Proof. intros x y z -> ->. reflexivity. Qed.

Lemma nat_exponential_injective : forall x z y,
  nat_exponential x y -> nat_exponential z y -> x = z.
Proof.
  intros x z y Hx Hz.
  apply (N.pow_inj_r 2 x z eq_refl).
  unfold nat_exponential in Hx, Hz. congruence.
Qed.

Lemma nat_exponential_monotone_iff : forall x z y w,
  nat_exponential x y -> nat_exponential z w ->
  (x < z <-> y < w).
Proof.
  intros x z y w Hx Hz.
  unfold nat_exponential in Hx, Hz. subst y. subst w.
  apply N.pow_lt_mono_r_iff. reflexivity.
Qed.

Lemma nat_exponential_monotone_le_iff : forall x z y w,
  nat_exponential x y -> nat_exponential z w ->
  (x <= z <-> y <= w).
Proof.
  intros x z y w Hx Hz.
  unfold nat_exponential in Hx, Hz. subst y. subst w.
  apply N.pow_le_mono_r_iff. reflexivity.
Qed.

Lemma nat_exponential_add_mul : forall x z y w,
  nat_exponential x y -> nat_exponential z w ->
  nat_exponential (x + z) (y * w).
Proof.
  intros x z y w -> ->. unfold nat_exponential.
  symmetry. apply N.pow_add_r.
Qed.

Lemma nat_exponential_exists_unique : forall x,
  exists! y, nat_exponential x y.
Proof.
  intro x. exists (2 ^ x).
  split; [reflexivity |].
  intros y Hy. now unfold nat_exponential in Hy.
Qed.

Lemma nat_exp_spec : forall x,
  nat_exponential x (nat_exp x).
Proof. reflexivity. Qed.

Lemma nat_exp_injective : forall x y,
  nat_exp x = nat_exp y -> x = y.
Proof.
  intros x y H. apply (N.pow_inj_r 2 x y eq_refl). exact H.
Qed.

Lemma nat_exp_zero : nat_exp 0 = 1.
Proof. reflexivity. Qed.

Lemma nat_exp_succ : forall x,
  nat_exp (x + 1) = 2 * nat_exp x.
Proof.
  intro x. unfold nat_exp.
  replace (x + 1) with (N.succ x) by lia.
  apply N.pow_succ_r'.
Qed.

Lemma nat_exp_even : forall x,
  nat_exp (2 * x) = nat_exp x * nat_exp x.
Proof.
  intro x. unfold nat_exp. rewrite <- N.pow_add_r. f_equal. lia.
Qed.

Lemma nat_exp_odd : forall x,
  nat_exp (2 * x + 1) = 2 * (nat_exp x * nat_exp x).
Proof.
  intro x. unfold nat_exp.
  rewrite <- N.pow_add_r, <- N.pow_succ_r'. f_equal. lia.
Qed.

Lemma nat_exp_add : forall x y,
  nat_exp (x + y) = nat_exp x * nat_exp y.
Proof. intros x y. unfold nat_exp. apply N.pow_add_r. Qed.

Print Assumptions nat_exponential_even.
Print Assumptions nat_exponential_odd.
Print Assumptions nat_exponential_exists_unique.
Print Assumptions nat_exp_add.
