(** Standard-natural Omega-one and smash arithmetic.

    Foundation adds Omega-one to weak nonstandard arithmetic in order to
    obtain exponentials whose exponents are products of binary lengths.  The
    standard natural model has total executable exponentiation, so the axiom
    is automatic and smash can be defined directly as [2^(|a|*|b|)].

    This removes all theory-strength, model, and choice hypotheses from the
    covered algebra.  The internal Omega-one sentence and Delta-zero graph of
    smash remain outside this module. *)

From Stdlib Require Import Lia NArith.NArith.
From Foundation.FirstOrder.Arithmetic Require Import Exponential.

Open Scope N_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Definition nat_omega1_holds : Prop :=
  forall x : N,
    exists y, nat_exponential (nat_length x * nat_length x) y.

Lemma standard_nat_omega1 : nat_omega1_holds.
Proof.
  intro x. exists (nat_exp (nat_length x * nat_length x)).
  apply nat_exp_spec.
Qed.

Lemma nat_exponential_square_length_exists_unique : forall x,
  exists! y, nat_exponential (nat_length x * nat_length x) y.
Proof. intro x. apply nat_exponential_exists_unique. Qed.

Definition nat_smash (a b : N) : N :=
  nat_exp (nat_length a * nat_length b).

Lemma nat_exponential_smash : forall a b,
  nat_exponential (nat_length a * nat_length b) (nat_smash a b).
Proof. intros a b. apply nat_exp_spec. Qed.

Lemma nat_smash_exists_unique : forall a b,
  exists! z,
    nat_exponential (nat_length a * nat_length b) z.
Proof. intros a b. apply nat_exponential_exists_unique. Qed.

Lemma nat_exponential_smash_one : forall a,
  nat_exponential (nat_length a) (nat_smash a 1).
Proof.
  intro a. unfold nat_smash.
  rewrite nat_length_one, N.mul_1_r.
  apply nat_exp_spec.
Qed.

Lemma nat_smash_pow2 : forall a b,
  nat_pow2 (nat_smash a b).
Proof.
  intros a b. exact (nat_exponential_range_pow2
    (@nat_exponential_smash a b)).
Qed.

Lemma nat_smash_pos : forall a b,
  0 < nat_smash a b.
Proof. intros a b. exact (nat_pow2_pos (@nat_smash_pow2 a b)). Qed.

Lemma nat_smash_exponent_lt : forall a b,
  nat_length a * nat_length b < nat_smash a b.
Proof.
  intros a b. exact (nat_exponential_lt (@nat_exponential_smash a b)).
Qed.

Lemma nat_length_smash : forall a b,
  nat_length (nat_smash a b) =
  nat_length a * nat_length b + 1.
Proof.
  intros a b. apply nat_exponential_length.
  apply nat_exponential_smash.
Qed.

Lemma nat_smash_zero_left : forall a,
  nat_smash 0 a = 1.
Proof. intro a. unfold nat_smash, nat_length. reflexivity. Qed.

Lemma nat_smash_zero_right : forall a,
  nat_smash a 0 = 1.
Proof. intro a. unfold nat_smash, nat_length. now rewrite N.mul_0_r. Qed.

Lemma nat_smash_comm : forall a b,
  nat_smash a b = nat_smash b a.
Proof.
  intros a b. unfold nat_smash. now rewrite N.mul_comm.
Qed.

(** This is the standard-model core of Foundation's [lt_smash_one_right]. *)
Lemma nat_lt_smash_one : forall a,
  a < nat_smash a 1.
Proof.
  intro a. unfold nat_smash.
  rewrite nat_length_one, N.mul_1_r.
  apply nat_lt_exp_length.
Qed.

Lemma nat_smash_one_le_double_add_one : forall a,
  nat_smash a 1 <= 2 * a + 1.
Proof.
  intro a. unfold nat_smash.
  rewrite nat_length_one, N.mul_1_r.
  unfold nat_exp, nat_length. rewrite <- N.succ_double_spec.
  exact (N.size_le a).
Qed.

Lemma nat_lt_smash_iff : forall a b c,
  a < nat_smash b c <->
  nat_length a <= nat_length b * nat_length c.
Proof.
  intros a b c.
  apply (@nat_exponential_lt_iff_length_le
    (nat_length b * nat_length c) (nat_smash b c) a).
  apply nat_exponential_smash.
Qed.

Lemma nat_smash_le_iff : forall a b c,
  nat_smash b c <= a <->
  nat_length b * nat_length c < nat_length a.
Proof.
  intros a b c.
  apply (@nat_exponential_le_iff_lt_length
    (nat_length b * nat_length c) (nat_smash b c) a).
  apply nat_exponential_smash.
Qed.

Lemma nat_lt_smash_one_iff : forall a b,
  a < nat_smash b 1 <-> nat_length a <= nat_length b.
Proof.
  intros a b. rewrite nat_lt_smash_iff, nat_length_one, N.mul_1_r.
  reflexivity.
Qed.

Lemma nat_smash_monotone : forall a1 a2 b1 b2,
  a1 <= b1 -> a2 <= b2 ->
  nat_smash a1 a2 <= nat_smash b1 b2.
Proof.
  intros a1 a2 b1 b2 H1 H2. unfold nat_smash, nat_exp.
  apply N.pow_le_mono_r; [discriminate |].
  apply N.mul_le_mono.
  - apply nat_length_monotone. exact H1.
  - apply nat_length_monotone. exact H2.
Qed.

Lemma nat_bexp_eq_smash : forall a b,
  nat_bexp (nat_smash a b) (nat_length a * nat_length b) =
  nat_smash a b.
Proof.
  intros a b. rewrite nat_bexp_of_lt.
  - reflexivity.
  - rewrite nat_length_smash.
    replace (nat_length a * nat_length b + 1) with
      (N.succ (nat_length a * nat_length b)) by lia.
    apply N.lt_succ_diag_r.
Qed.

Lemma nat_smash_two_mul : forall a b,
  0 < b ->
  nat_smash a (2 * b) = nat_smash a b * nat_smash a 1.
Proof.
  intros a b Hb. unfold nat_smash.
  rewrite nat_length_one, N.mul_1_r.
  rewrite nat_length_two_mul_of_pos by exact Hb.
  rewrite N.mul_add_distr_l.
  rewrite N.mul_1_r.
  rewrite nat_exp_add. reflexivity.
Qed.

Lemma nat_smash_two_mul_le_square : forall a b,
  nat_smash a (2 * b) <= nat_smash a b * nat_smash a b.
Proof.
  intros a b. destruct (N.eq_dec b 0) as [-> | Hb].
  - rewrite nat_smash_zero_right, nat_smash_zero_right.
    unfold nat_smash, nat_length. reflexivity.
  - rewrite nat_smash_two_mul by exact (proj1 (N.neq_0_lt_0 b) Hb).
    apply N.mul_le_mono_nonneg_l; [apply N.le_0_l |].
    apply nat_smash_monotone; [apply N.le_refl |].
    apply N.nlt_ge. intro Hlt. apply Hb.
    exact (proj1 (N.lt_1_r b) Hlt).
Qed.

Print Assumptions standard_nat_omega1.
Print Assumptions nat_lt_smash_iff.
Print Assumptions nat_smash_two_mul_le_square.
