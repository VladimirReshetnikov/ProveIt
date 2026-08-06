(** Binary logarithm, length, bounded exponentiation, and finite bits.

    Foundation defines these operations inside weak nonstandard arithmetic
    from its internally certified exponential graph.  On standard binary
    naturals, Stdlib's [N.log2], [N.size], and [N.testbit] are the canonical
    executable operations.  Using them directly gives stronger constructive
    statements and factors all later bit arithmetic through one small API.

    Formula graphs, hierarchy certificates, and arbitrary-model absoluteness
    remain outside this module; none is postulated. *)

From Stdlib Require Import Bool.Bool Lia NArith.NArith.
From Foundation.FirstOrder.Arithmetic.Exponential Require Import
  Pow2 PPow2 Exp Bit.

Open Scope N_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(** Reusable discrete-order bridge for binary interval proofs. *)
Lemma N_succ_le_of_lt : forall a b : N,
  a < b -> N.succ a <= b.
Proof.
  intros a b H.
  apply (proj1 (N.lt_succ_r (N.succ a) b)).
  apply (proj1 (N.succ_lt_mono a b)). exact H.
Qed.

Definition nat_log (a : N) : N := N.log2 a.

Lemma nat_log_zero : nat_log 0 = 0.
Proof. reflexivity. Qed.

Lemma nat_log_one : nat_log 1 = 0.
Proof. exact N.log2_1. Qed.

Lemma nat_log_two : nat_log 2 = 1.
Proof. exact N.log2_2. Qed.

Lemma nat_log_le_self : forall a,
  nat_log a <= a.
Proof. intro a. apply N.log2_le_lin. apply N.le_0_l. Qed.

Lemma nat_log_lt_self_of_pos : forall a,
  0 < a -> nat_log a < a.
Proof. exact N.log2_lt_lin. Qed.

(** Exact floor-logarithm interval. *)
Lemma nat_log_bounds : forall a,
  0 < a ->
  2 ^ nat_log a <= a /\ a < 2 * 2 ^ nat_log a.
Proof.
  intros a Ha. destruct (N.log2_spec a Ha) as [Hlo Hhi].
  split; [exact Hlo |].
  unfold nat_log. now rewrite <- N.pow_succ_r'.
Qed.

Lemma nat_log_unique : forall a k,
  2 ^ k <= a -> a < 2 * 2 ^ k -> nat_log a = k.
Proof.
  intros a k Hlo Hhi. unfold nat_log.
  apply N.log2_unique; [apply N.le_0_l |].
  split; [exact Hlo |]. now rewrite N.pow_succ_r'.
Qed.

Lemma nat_log_exp : forall k,
  nat_log (2 ^ k) = k.
Proof.
  intro k. unfold nat_log. apply N.log2_pow2. apply N.le_0_l.
Qed.

Lemma nat_exponential_log : forall x y,
  nat_exponential x y -> nat_log y = x.
Proof. intros x y ->. apply nat_log_exp. Qed.

Lemma nat_exponential_of_pow2 : forall p,
  nat_pow2 p -> nat_exponential (nat_log p) p.
Proof.
  intros p [k ->]. unfold nat_exponential. now rewrite nat_log_exp.
Qed.

Lemma nat_log_two_mul_of_pos : forall a,
  0 < a -> nat_log (2 * a) = nat_log a + 1.
Proof.
  intros a Ha. unfold nat_log. rewrite N.log2_double by exact Ha. lia.
Qed.

Lemma nat_log_two_mul_add_one_of_pos : forall a,
  0 < a -> nat_log (2 * a + 1) = nat_log a + 1.
Proof.
  intros a Ha. unfold nat_log.
  rewrite N.log2_succ_double by exact Ha. lia.
Qed.

Lemma nat_log_monotone : forall a b,
  a <= b -> nat_log a <= nat_log b.
Proof. exact N.log2_le_mono. Qed.

Lemma nat_log_mul_pow2 : forall a p,
  0 < a -> nat_pow2 p ->
  nat_log (a * p) = nat_log a + nat_log p.
Proof.
  intros a p Ha [k ->]. unfold nat_log.
  rewrite N.log2_mul_pow2 by (assumption || apply N.le_0_l).
  rewrite N.log2_pow2 by apply N.le_0_l. lia.
Qed.

Lemma nat_log_mul_exp : forall a i,
  0 < a -> nat_log (a * nat_exp i) = nat_log a + i.
Proof.
  intros a i Ha. unfold nat_exp.
  rewrite nat_log_mul_pow2; [|exact Ha | apply nat_pow2_power].
  now rewrite nat_log_exp.
Qed.

(** Appending a lower binary block does not change the leading logarithm. *)
Lemma nat_log_mul_pow2_add_of_lt : forall a p b,
  0 < a -> nat_pow2 p -> b < p ->
  nat_log (a * p + b) = nat_log a + nat_log p.
Proof.
  intros a p b Ha [k ->] Hb. rewrite nat_log_exp.
  apply nat_log_unique.
  - rewrite N.pow_add_r.
    eapply N.le_trans.
    + apply N.mul_le_mono_nonneg_r; [apply N.le_0_l |].
      exact (proj1 (nat_log_bounds Ha)).
    + apply N.le_add_r.
  - eapply N.lt_le_trans.
    + eapply N.lt_le_trans.
      * apply N.add_lt_mono_l. exact Hb.
      * replace (a * 2 ^ k + 2 ^ k) with
          ((N.succ a) * 2 ^ k) by
            (replace (N.succ a) with (a + 1) by lia; nia).
        apply N.mul_le_mono_nonneg_r; [apply N.le_0_l |].
        apply N_succ_le_of_lt.
        exact (proj2 (nat_log_bounds Ha)).
    + rewrite N.pow_add_r.
      replace ((2 * 2 ^ nat_log a) * 2 ^ k) with
        (2 * (2 ^ nat_log a * 2 ^ k)) by nia.
      apply N.le_refl.
Qed.

Lemma nat_log_mul_exp_add_of_lt : forall a b i,
  0 < a -> b < nat_exp i ->
  nat_log (a * nat_exp i + b) = nat_log a + i.
Proof.
  intros a b i Ha Hb. unfold nat_exp in *.
  rewrite nat_log_mul_pow2_add_of_lt;
    [now rewrite nat_log_exp | exact Ha | apply nat_pow2_power | exact Hb].
Qed.

(** Binary length, with zero assigned length zero. *)
Definition nat_length (a : N) : N := N.size a.

Lemma nat_length_zero : nat_length 0 = 0.
Proof. reflexivity. Qed.

Lemma nat_length_one : nat_length 1 = 1.
Proof. reflexivity. Qed.

Lemma nat_length_of_nonzero : forall a,
  a <> 0 -> nat_length a = N.succ (nat_log a).
Proof. intros a Ha. unfold nat_length, nat_log. apply N.size_log2. exact Ha. Qed.

Lemma nat_length_of_pos : forall a,
  0 < a -> nat_length a = nat_log a + 1.
Proof.
  intros a Ha. rewrite nat_length_of_nonzero.
  - lia.
  - exact (proj2 (N.neq_0_lt_0 a) Ha).
Qed.

Lemma nat_length_pos_iff : forall a,
  0 < nat_length a <-> 0 < a.
Proof.
  intro a. destruct (N.eq_dec a 0) as [-> | Ha].
  - reflexivity.
  - rewrite nat_length_of_nonzero by exact Ha.
    split; [intro; exact (proj1 (N.neq_0_lt_0 a) Ha) | lia].
Qed.

Lemma nat_length_eq_zero_iff : forall a,
  nat_length a = 0 <-> a = 0.
Proof.
  intro a. destruct (N.eq_dec a 0) as [-> | Ha]; [reflexivity |].
  split; [|contradiction]. intro H.
  pose proof (proj2 (nat_length_pos_iff a)
    (proj1 (N.neq_0_lt_0 a) Ha)). lia.
Qed.

Lemma nat_length_le_self : forall a,
  nat_length a <= a.
Proof.
  intro a. destruct (N.eq_dec a 0) as [-> | Ha]; [reflexivity |].
  rewrite nat_length_of_nonzero by exact Ha.
  apply (proj1 (N.lt_succ_r (N.succ (nat_log a)) a)).
  apply (proj1 (N.succ_lt_mono (nat_log a) a)).
  exact (N.log2_lt_lin a (proj1 (N.neq_0_lt_0 a) Ha)).
Qed.

Lemma nat_exponential_length : forall x y,
  nat_exponential x y -> nat_length y = x + 1.
Proof.
  intros x y ->. rewrite nat_length_of_nonzero.
  - unfold nat_log. rewrite N.log2_pow2 by apply N.le_0_l. lia.
  - apply N.pow_nonzero. discriminate.
Qed.

Lemma nat_length_exp : forall x,
  nat_length (nat_exp x) = x + 1.
Proof. intro x. apply nat_exponential_length. apply nat_exp_spec. Qed.

(** Two elementary square-root estimates used by the standard Nuon bounds. *)
Lemma nat_two_mul_sqrt_le_self : forall a,
  2 * N.sqrt a <= a + 1.
Proof.
  intro a. pose proof (proj1 (N.sqrt_spec a (N.le_0_l _))) as Hlow.
  simpl in Hlow. nia.
Qed.

Lemma nat_sqrt_pos_iff : forall a,
  0 < N.sqrt a <-> 0 < a.
Proof.
  intro a. split.
  - intro H. pose proof (proj1 (N.sqrt_spec a (N.le_0_l _))) as Hlow.
    simpl in Hlow. nia.
  - intro H. destruct (N.eq_dec (N.sqrt a) 0) as [Hz | Hz]; [|lia].
    pose proof (proj2 (N.sqrt_spec a (N.le_0_l _))) as Hhi.
    simpl in Hhi. lia.
Qed.

Lemma nat_length_two_mul_of_pos : forall a,
  0 < a -> nat_length (2 * a) = nat_length a + 1.
Proof.
  intros a Ha. rewrite !nat_length_of_pos.
  - rewrite nat_log_two_mul_of_pos by exact Ha. lia.
  - nia.
  - nia.
Qed.

Lemma nat_length_two_mul_add_one : forall a,
  nat_length (2 * a + 1) = nat_length a + 1.
Proof.
  intro a. destruct (N.eq_dec a 0) as [-> | Ha]; [reflexivity |].
  rewrite !nat_length_of_pos.
  - rewrite nat_log_two_mul_add_one_of_pos.
    + lia.
    + exact (proj1 (N.neq_0_lt_0 a) Ha).
  - nia.
  - nia.
Qed.

Lemma nat_length_monotone : forall a b,
  a <= b -> nat_length a <= nat_length b.
Proof.
  intros a b Hab. destruct (N.eq_dec a 0) as [-> | Ha]; [apply N.le_0_l |].
  assert (Hb : b <> 0).
  { intro E. subst b. apply Ha. exact (proj1 (N.le_0_r a) Hab). }
  rewrite !nat_length_of_nonzero by assumption.
  apply (proj1 (N.succ_le_mono (nat_log a) (nat_log b))).
  apply nat_log_monotone. exact Hab.
Qed.

Lemma nat_pos_of_lt_length : forall a b,
  a < nat_length b -> 0 < b.
Proof.
  intros a b H.
  apply (proj1 (nat_length_pos_iff b)). lia.
Qed.

Lemma nat_le_log_of_lt_length : forall a b,
  a < nat_length b -> a <= nat_log b.
Proof.
  intros a b H.
  rewrite nat_length_of_pos in H by now apply nat_pos_of_lt_length with a.
  lia.
Qed.

Lemma nat_exp_le_iff_le_log : forall i a,
  0 < a -> (nat_exp i <= a <-> i <= nat_log a).
Proof.
  intros i a Ha. unfold nat_exp, nat_log.
  apply N.log2_le_pow2. exact Ha.
Qed.

Lemma nat_exponential_le_iff_lt_length : forall x y a,
  nat_exponential x y ->
  (y <= a <-> x < nat_length a).
Proof.
  intros x y a Hexp. unfold nat_exponential in Hexp. subst y.
  destruct (N.eq_dec a 0) as [-> | Ha].
  - split; intro H.
    + exfalso. apply (N.pow_nonzero 2 x ltac:(discriminate)). nia.
    + exfalso. exact (N.nlt_0_r x H).
  - rewrite nat_length_of_nonzero by exact Ha.
    rewrite nat_exp_le_iff_le_log by exact (proj1 (N.neq_0_lt_0 a) Ha).
    lia.
Qed.

Lemma nat_exponential_lt_iff_length_le : forall x y a,
  nat_exponential x y ->
  (a < y <-> nat_length a <= x).
Proof.
  intros x y a Hexp. split.
  - intro Hlt. apply N.nlt_ge. intro Hnot.
    apply (N.lt_irrefl y).
    eapply N.le_lt_trans; [|exact Hlt].
    exact (proj2 (@nat_exponential_le_iff_lt_length x y a Hexp) Hnot).
  - intro Hle. apply N.nle_gt. intro Hnot.
    apply (N.lt_irrefl (nat_length a)).
    eapply N.le_lt_trans; [exact Hle |].
    exact (proj1 (@nat_exponential_le_iff_lt_length x y a Hexp) Hnot).
Qed.

Lemma nat_lt_exp_length : forall a,
  a < nat_exp (nat_length a).
Proof. intro a. unfold nat_exp, nat_length. apply N.size_gt. Qed.

Lemma nat_length_mul_exp : forall a i,
  0 < a ->
  nat_length (a * nat_exp i) = nat_length a + i.
Proof.
  intros a i Ha. rewrite !nat_length_of_pos.
  - rewrite nat_log_mul_exp by exact Ha. lia.
  - exact Ha.
  - apply N.mul_pos_pos; [exact Ha |].
    unfold nat_exp. apply (proj1 (N.neq_0_lt_0 (2 ^ i))).
    apply N.pow_nonzero. discriminate.
Qed.

Lemma nat_length_mul_pow2_add_of_lt : forall a p b,
  0 < a -> nat_pow2 p -> b < p ->
  nat_length (a * p + b) = nat_length a + nat_log p.
Proof.
  intros a p b Ha Hp Hb. rewrite !nat_length_of_pos.
  - rewrite nat_log_mul_pow2_add_of_lt by assumption. lia.
  - pose proof (nat_pow2_pos Hp). nia.
  - pose proof (nat_pow2_pos Hp). nia.
Qed.

Lemma nat_length_mul_exp_add_of_lt : forall a b i,
  0 < a -> b < nat_exp i ->
  nat_length (a * nat_exp i + b) = nat_length a + i.
Proof.
  intros a b i Ha Hb. unfold nat_exp in *.
  rewrite nat_length_mul_pow2_add_of_lt;
    [now rewrite nat_log_exp | exact Ha | apply nat_pow2_power | exact Hb].
Qed.

(** The standard-model form of Foundation's [sq_len_le_three_mul].  Binary
    induction exposes the same even/odd decomposition used by the source's
    polynomial induction, while [nat_length_le_self] supplies the only
    numerical estimate needed in each successor branch. *)
Lemma nat_sq_length_le_three_mul : forall a,
  nat_length a ^ 2 <= 3 * a.
Proof.
  intro a.
  induction a using N.binary_induction.
  - simpl. lia.
  - destruct (N.eq_dec a 0) as [-> | Hn].
    + simpl. lia.
    + assert (Hpos : 0 < a) by
        (apply (proj1 (N.neq_0_lt_0 a)); exact Hn).
      rewrite nat_length_two_mul_of_pos by exact Hpos.
      pose proof (@nat_length_le_self a) as Hlen.
      assert (Hone : 1 <= a) by lia.
      nia.
  - destruct (N.eq_dec a 0) as [-> | Hn].
    + simpl. lia.
    + assert (Hpos : 0 < a) by
        (apply (proj1 (N.neq_0_lt_0 a)); exact Hn).
      rewrite nat_length_two_mul_add_one.
      pose proof (@nat_length_le_self a) as Hlen.
      assert (Hone : 1 <= a) by lia.
      nia.
Qed.

(** [nat_bexp a x] is [2^x] inside the binary length of [a], and zero
    outside it.  Unlike the source choice construction, it is executable. *)
Definition nat_bexp (a x : N) : N :=
  if x <? nat_length a then nat_exp x else 0.

Lemma nat_bexp_of_lt : forall a x,
  x < nat_length a -> nat_bexp a x = nat_exp x.
Proof.
  intros a x H. unfold nat_bexp.
  now rewrite (proj2 (N.ltb_lt x (nat_length a)) H).
Qed.

Lemma nat_bexp_of_le : forall a x,
  nat_length a <= x -> nat_bexp a x = 0.
Proof.
  intros a x H. unfold nat_bexp.
  now rewrite (proj2 (N.ltb_ge x (nat_length a)) H).
Qed.

Lemma nat_bexp_exponential_iff : forall a x,
  nat_exponential x (nat_bexp a x) <-> x < nat_length a.
Proof.
  intros a x. split.
  - intro H. apply N.nle_gt. intro Hle.
    rewrite nat_bexp_of_le in H by exact Hle.
    exact (N.lt_irrefl 0 (nat_exponential_range_pos H)).
  - intro H. rewrite nat_bexp_of_lt by exact H. apply nat_exp_spec.
Qed.

Lemma nat_bexp_le_self : forall a x,
  nat_bexp a x <= a.
Proof.
  intros a x. destruct (N.lt_ge_cases x (nat_length a)) as [Hlt | Hle].
  - rewrite nat_bexp_of_lt by exact Hlt.
    apply (proj2 (@nat_exp_le_iff_le_log x a
      (nat_pos_of_lt_length Hlt))).
    exact (nat_le_log_of_lt_length Hlt).
  - rewrite nat_bexp_of_le by exact Hle. apply N.le_0_l.
Qed.

Lemma nat_bexp_monotone_iff : forall a i j,
  i < nat_length a -> j < nat_length a ->
  (nat_bexp a i < nat_bexp a j <-> i < j).
Proof.
  intros a i j Hi Hj. rewrite !nat_bexp_of_lt by assumption.
  symmetry. apply N.pow_lt_mono_r_iff. reflexivity.
Qed.

Lemma nat_bexp_monotone_le_iff : forall a i j,
  i < nat_length a -> j < nat_length a ->
  (nat_bexp a i <= nat_bexp a j <-> i <= j).
Proof.
  intros a i j Hi Hj. rewrite !nat_bexp_of_lt by assumption.
  symmetry. apply N.pow_le_mono_r_iff. reflexivity.
Qed.

(** Cross-base comparison: once both bounded exponents are in range, the
    bases are irrelevant and order is exactly order of the indices. *)
Lemma nat_bexp_monotone_cross_iff : forall a1 i1 a2 i2,
  i1 < nat_length a1 -> i2 < nat_length a2 ->
  (nat_bexp a1 i1 < nat_bexp a2 i2 <-> i1 < i2).
Proof.
  intros a1 i1 a2 i2 H1 H2.
  rewrite !nat_bexp_of_lt by assumption.
  unfold nat_exp.
  symmetry. apply N.pow_lt_mono_r_iff. reflexivity.
Qed.

Lemma nat_bexp_monotone_cross_le_iff : forall a1 i1 a2 i2,
  i1 < nat_length a1 -> i2 < nat_length a2 ->
  (nat_bexp a1 i1 <= nat_bexp a2 i2 <-> i1 <= i2).
Proof.
  intros a1 i1 a2 i2 H1 H2.
  rewrite !nat_bexp_of_lt by assumption.
  unfold nat_exp.
  symmetry. apply N.pow_le_mono_r_iff. reflexivity.
Qed.

Lemma nat_bexp_two_mul : forall a a' x,
  2 * x < nat_length a -> x < nat_length a' ->
  nat_bexp a (2 * x) = (nat_bexp a' x) ^ 2.
Proof.
  intros a a' x Ha Ha'.
  rewrite nat_bexp_of_lt by exact Ha.
  rewrite nat_bexp_of_lt by exact Ha'.
  unfold nat_exp.
  rewrite <- N.pow_mul_r.
  f_equal. lia.
Qed.

Lemma nat_bexp_two_mul_succ : forall a i,
  nat_bexp (2 * a) (i + 1) = 2 * nat_bexp a i.
Proof.
  intros a i.
  destruct (N.eq_dec a 0) as [Ha | Ha].
  - subst a.
    change (nat_bexp 0 (i + 1) = 2 * nat_bexp 0 i).
    assert (H1 : nat_length 0 <= i + 1).
    { rewrite nat_length_zero. lia. }
    assert (H0 : nat_length 0 <= i).
    { rewrite nat_length_zero. apply N.le_0_l. }
    rewrite (nat_bexp_of_le H1), (nat_bexp_of_le H0).
    reflexivity.
  - destruct (N.lt_ge_cases i (nat_length a)) as [Hi | Hi].
    + rewrite nat_bexp_of_lt.
      2:{ rewrite nat_length_two_mul_of_pos; lia. }
      rewrite nat_bexp_of_lt by exact Hi.
      unfold nat_exp.
      rewrite N.add_1_r, N.pow_succ_r'.
      reflexivity.
    + rewrite nat_bexp_of_le by (rewrite nat_length_two_mul_of_pos; lia).
      rewrite nat_bexp_of_le by exact Hi.
      reflexivity.
Qed.

Lemma nat_bexp_two_mul_add_one_succ : forall a i,
  nat_bexp (2 * a + 1) (i + 1) = 2 * nat_bexp a i.
Proof.
  intros a i.
  destruct (N.lt_ge_cases i (nat_length a)) as [Hi | Hi].
  - rewrite nat_bexp_of_lt.
    2:{ rewrite nat_length_two_mul_add_one; lia. }
    rewrite nat_bexp_of_lt by exact Hi.
    unfold nat_exp.
    rewrite N.add_1_r, N.pow_succ_r'.
    reflexivity.
  - rewrite nat_bexp_of_le by (rewrite nat_length_two_mul_add_one; lia).
    rewrite nat_bexp_of_le by exact Hi.
    reflexivity.
Qed.

Lemma nat_pow_four_le_pow_four : forall a b,
  a ^ 4 <= b ^ 4 <-> a <= b.
Proof.
  intros a b. symmetry.
  apply (N.pow_le_mono_l_iff a b 4). discriminate.
Qed.

Lemma nat_bexp_four_mul : forall a a' x,
  4 * x < nat_length a -> x < nat_length a' ->
  nat_bexp a (4 * x) = (nat_bexp a' x) ^ 4.
Proof.
  intros a a' x Ha Ha'.
  rewrite nat_bexp_of_lt by exact Ha.
  rewrite nat_bexp_of_lt by exact Ha'.
  unfold nat_exp.
  rewrite <- N.pow_mul_r.
  f_equal. lia.
Qed.

Lemma nat_bexp_eq_of_lt_length : forall a b i,
  i < nat_length a -> i < nat_length b ->
  nat_bexp a i = nat_bexp b i.
Proof. intros a b i Ha Hb. now rewrite !nat_bexp_of_lt by assumption. Qed.

Lemma nat_bexp_pow2 : forall a x,
  x < nat_length a -> nat_pow2 (nat_bexp a x).
Proof.
  intros a x H. rewrite nat_bexp_of_lt by exact H.
  unfold nat_exp. apply nat_pow2_power.
Qed.

Lemma nat_bexp_pos : forall a x,
  x < nat_length a -> 0 < nat_bexp a x.
Proof.
  intros a x H. exact (nat_pow2_pos (nat_bexp_pow2 H)).
Qed.

Lemma nat_lt_bexp : forall a x,
  x < nat_length a -> x < nat_bexp a x.
Proof.
  intros a x H. rewrite nat_bexp_of_lt by exact H.
  unfold nat_exp. apply N.pow_gt_lin_r. reflexivity.
Qed.

Lemma nat_log_bexp : forall a x,
  x < nat_length a -> nat_log (nat_bexp a x) = x.
Proof.
  intros a x H. rewrite nat_bexp_of_lt by exact H.
  unfold nat_exp. apply nat_log_exp.
Qed.

Lemma nat_length_bexp : forall a x,
  x < nat_length a -> nat_length (nat_bexp a x) = x + 1.
Proof.
  intros a x H. rewrite nat_bexp_of_lt by exact H.
  apply nat_length_exp.
Qed.

Lemma nat_bexp_zero : forall x,
  nat_bexp 0 x = 0.
Proof. intro x. apply nat_bexp_of_le. apply N.le_0_l. Qed.

Lemma nat_bexp_pos_zero : forall a,
  0 < a -> nat_bexp a 0 = 1.
Proof.
  intros a Ha. rewrite nat_bexp_of_lt.
  - reflexivity.
  - apply (proj2 (nat_length_pos_iff a)). exact Ha.
Qed.

Lemma nat_bexp_add : forall a x y,
  x + y < nat_length a ->
  nat_bexp a (x + y) = nat_bexp a x * nat_bexp a y.
Proof.
  intros a x y H. rewrite !nat_bexp_of_lt.
  - apply nat_exp_add.
  - eapply N.le_lt_trans; [apply N.le_add_l | exact H].
  - eapply N.le_lt_trans; [apply N.le_add_r | exact H].
  - exact H.
Qed.

(** A finite binary digit as the natural number zero or one. *)
Definition nat_fbit (a i : N) : N := N.b2n (N.testbit a i).

Lemma nat_fbit_le_one : forall a i,
  nat_fbit a i <= 1.
Proof. intros a i. apply N.b2n_le_1. Qed.

Lemma nat_fbit_lt_two : forall a i,
  nat_fbit a i < 2.
Proof. intros a i. pose proof (@nat_fbit_le_one a i). lia. Qed.

Lemma nat_fbit_eq_one_iff : forall a i,
  nat_fbit a i = 1 <-> nat_bit i a.
Proof.
  intros a i. rewrite nat_bit_mem_iff. unfold nat_fbit.
  destruct (N.testbit a i); simpl; intuition discriminate.
Qed.

Lemma nat_fbit_eq_zero_iff : forall a i,
  nat_fbit a i = 0 <-> ~ nat_bit i a.
Proof.
  intros a i. rewrite nat_bit_mem_iff. unfold nat_fbit.
  destruct (N.testbit a i); simpl; intuition discriminate.
Qed.

Lemma nat_fbit_eq_zero_of_le : forall a i,
  nat_length a <= i -> nat_fbit a i = 0.
Proof.
  intros a i Hle. unfold nat_fbit.
  destruct (N.eq_dec a 0) as [-> | Ha].
  - reflexivity.
  - rewrite (N.bits_above_log2 a i).
    + reflexivity.
    + rewrite nat_length_of_nonzero in Hle by exact Ha.
      eapply N.lt_le_trans; [apply N.lt_succ_diag_r | exact Hle].
Qed.

Lemma nat_fbit_zero : forall i,
  nat_fbit 0 i = 0.
Proof. reflexivity. Qed.

Lemma nat_fbit_double_succ : forall a i,
  nat_fbit (2 * a) (N.succ i) = nat_fbit a i.
Proof.
  intros a i. unfold nat_fbit.
  now rewrite N.testbit_even_succ by apply N.le_0_l.
Qed.

Lemma nat_fbit_double_add_one_succ : forall a i,
  nat_fbit (2 * a + 1) (N.succ i) = nat_fbit a i.
Proof.
  intros a i. unfold nat_fbit.
  now rewrite N.testbit_odd_succ by apply N.le_0_l.
Qed.

Lemma nat_fbit_double_zero : forall a,
  nat_fbit (2 * a) 0 = 0.
Proof.
  intro a. unfold nat_fbit. now rewrite N.testbit_even_0.
Qed.

Lemma nat_fbit_double_add_one_zero : forall a,
  nat_fbit (2 * a + 1) 0 = 1.
Proof.
  intro a. unfold nat_fbit. now rewrite N.testbit_odd_0.
Qed.

Print Assumptions nat_log_bounds.
Print Assumptions nat_exponential_le_iff_lt_length.
Print Assumptions nat_bexp_add.
Print Assumptions nat_fbit_eq_one_iff.
