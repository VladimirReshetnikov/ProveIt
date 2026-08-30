import FabiusFunction.QBinomialInversion

/-!
# Elementary finite q-Pochhammer identities

This module records the elementary base-reversal, terminating-factor, and
adjacent Gaussian-coefficient identities in forms that keep their boundary
conditions explicit.  The polynomial identities are stated over arbitrary
commutative rings and do not divide by q-Pochhammer factors.  Quotient forms
are separate field corollaries carrying exactly the nonvanishing hypotheses
needed for their displayed denominators.

In particular, `prod_pow_sub_pow_eq_finiteQPochhammerIn` is the root-safe
numerator behind the terminating specialization `(q ^ N)⁻¹`, while the two
adjacent cross identities remain valid at roots of unity even when neither
corresponding ratio is defined.

## Main results

* `finiteQPochhammerIn_base_reversal_units` and
  `finiteQPochhammerIn_inv_base_reversal_units` give both base-reversal
  orientations for unit parameters over a commutative ring.
* `finiteQPochhammerIn_base_reversal` and
  `finiteQPochhammerIn_inv_base_reversal` are the exact field wrappers, with
  the necessary assumptions `a != 0` and `q != 0`.
* `prod_pow_sub_pow_eq_finiteQPochhammerIn` is the denominator-free product
  identity underlying the terminating specialization.
* `pow_mul_finiteQPochhammerIn_inv_pow_eq`,
  `finiteQPochhammerIn_inv_pow_eq_self_div`, and
  `finiteQPochhammerIn_inv_pow_eq_zero_of_lt` cover the two ranges of the
  specialization at `(q ^ N)⁻¹`.
* `one_sub_mul_gaussianBinomial_one` clears the first Gaussian column.
* `gaussianBinomial_adjacent_mul` and
  `gaussianBinomial_row_adjacent_mul` are root-safe adjacent identities;
  their `..._div` corollaries state the corresponding field ratios.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-! ## Base reversal -/

/-- **Base reversal for units.**  If `a` and `q` are units in a commutative
ring, then

`(a;q)_n = (-a)^n q^(n choose 2) (a⁻¹;q⁻¹)_n`.

Using units makes both invertibility requirements structural and keeps the
identity valid over rings with zero divisors. -/
theorem finiteQPochhammerIn_base_reversal_units
    {R : Type*} [CommRing R] (a q : Rˣ) (n : ℕ) :
    finiteQPochhammerIn (a : R) (q : R) n =
      (- (a : R)) ^ n * (q : R) ^ n.choose 2 *
        finiteQPochhammerIn ((a⁻¹ : Rˣ) : R) ((q⁻¹ : Rˣ) : R) n := by
  have hfactor (j : ℕ) :
      1 - (a : R) * (q : R) ^ j =
        (- (a : R) * (q : R) ^ j) *
          (1 - ((a⁻¹ : Rˣ) : R) * ((q⁻¹ : Rˣ) : R) ^ j) := by
    have hainv : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by
      simp
    have hqinv :
        (q : R) ^ j * ((q⁻¹ : Rˣ) : R) ^ j = 1 := by
      rw [← mul_pow]
      simp
    have hcancel :
        ((a : R) * (q : R) ^ j) *
            (((a⁻¹ : Rˣ) : R) * ((q⁻¹ : Rˣ) : R) ^ j) = 1 := by
      calc
        ((a : R) * (q : R) ^ j) *
              (((a⁻¹ : Rˣ) : R) * ((q⁻¹ : Rˣ) : R) ^ j) =
            ((a : R) * ((a⁻¹ : Rˣ) : R)) *
              ((q : R) ^ j * ((q⁻¹ : Rˣ) : R) ^ j) := by
                ring
        _ = 1 := by rw [hainv, hqinv, one_mul]
    have hnegcancel :
        (- (a : R) * (q : R) ^ j) *
            (((a⁻¹ : Rˣ) : R) * ((q⁻¹ : Rˣ) : R) ^ j) = -1 := by
      calc
        (- (a : R) * (q : R) ^ j) *
              (((a⁻¹ : Rˣ) : R) * ((q⁻¹ : Rˣ) : R) ^ j) =
            -(((a : R) * (q : R) ^ j) *
              (((a⁻¹ : Rˣ) : R) * ((q⁻¹ : Rˣ) : R) ^ j)) := by
                ring
        _ = -1 := by rw [hcancel]
    calc
      1 - (a : R) * (q : R) ^ j =
          (- (a : R) * (q : R) ^ j) - (-1) := by ring
      _ = (- (a : R) * (q : R) ^ j) *
          (1 - ((a⁻¹ : Rˣ) : R) * ((q⁻¹ : Rˣ) : R) ^ j) := by
            rw [mul_sub, mul_one, hnegcancel]
  have hprefactor :
      (∏ j ∈ Finset.range n, (- (a : R)) * (q : R) ^ j) =
        (- (a : R)) ^ n * (q : R) ^ n.choose 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
      Nat.choose_two_right]
  unfold finiteQPochhammerIn
  calc
    (∏ j ∈ Finset.range n, (1 - (a : R) * (q : R) ^ j)) =
        ∏ j ∈ Finset.range n,
          ((- (a : R) * (q : R) ^ j) *
            (1 - ((a⁻¹ : Rˣ) : R) * ((q⁻¹ : Rˣ) : R) ^ j)) := by
      apply Finset.prod_congr rfl
      intro j _hj
      exact hfactor j
    _ = (∏ j ∈ Finset.range n, (- (a : R)) * (q : R) ^ j) *
          ∏ j ∈ Finset.range n,
            (1 - ((a⁻¹ : Rˣ) : R) * ((q⁻¹ : Rˣ) : R) ^ j) := by
      rw [Finset.prod_mul_distrib]
    _ = (- (a : R)) ^ n * (q : R) ^ n.choose 2 *
          ∏ j ∈ Finset.range n,
            (1 - ((a⁻¹ : Rˣ) : R) * ((q⁻¹ : Rˣ) : R) ^ j) := by
      rw [hprefactor]

/-- **Inverse-base reversal for units.**  This is the second standard
orientation of base reversal:

`(a;q⁻¹)_n = (-a)^n (q⁻¹)^(n choose 2) (a⁻¹;q)_n`.

It is named separately so downstream exactness claims need not rely on an
implicit substitution into the first orientation. -/
theorem finiteQPochhammerIn_inv_base_reversal_units
    {R : Type*} [CommRing R] (a q : Rˣ) (n : ℕ) :
    finiteQPochhammerIn (a : R) ((q⁻¹ : Rˣ) : R) n =
      (- (a : R)) ^ n * ((q⁻¹ : Rˣ) : R) ^ n.choose 2 *
        finiteQPochhammerIn ((a⁻¹ : Rˣ) : R) (q : R) n := by
  simpa only [inv_inv] using
    finiteQPochhammerIn_base_reversal_units a q⁻¹ n

/-- **Field-valued base reversal.**  For nonzero `a` and `q`,

`(a;q)_n = (-a)^n q^(n choose 2) (a⁻¹;q⁻¹)_n`.

Both nonzero assumptions are necessary for this numerical inverse notation;
the unit theorem above is the ring-generic source. -/
theorem finiteQPochhammerIn_base_reversal
    {K : Type*} [Field K] (a q : K)
    (ha : a ≠ 0) (hq : q ≠ 0) (n : ℕ) :
    finiteQPochhammerIn a q n =
      (-a) ^ n * q ^ n.choose 2 *
        finiteQPochhammerIn a⁻¹ q⁻¹ n := by
  simpa only [Units.val_mk0, Units.val_inv_eq_inv_val] using
    finiteQPochhammerIn_base_reversal_units
      (Units.mk0 a ha) (Units.mk0 q hq) n

/-- **Field-valued inverse-base reversal.**  For nonzero `a` and `q`,

`(a;q⁻¹)_n = (-a)^n (q⁻¹)^(n choose 2) (a⁻¹;q)_n`.

This explicit corollary is the second displayed base-reversal orientation,
including the repaired `q != 0` boundary required by inverse powers. -/
theorem finiteQPochhammerIn_inv_base_reversal
    {K : Type*} [Field K] (a q : K)
    (ha : a ≠ 0) (hq : q ≠ 0) (n : ℕ) :
    finiteQPochhammerIn a q⁻¹ n =
      (-a) ^ n * (q⁻¹) ^ n.choose 2 *
        finiteQPochhammerIn a⁻¹ q n := by
  simpa only [Units.val_mk0, Units.val_inv_eq_inv_val] using
    finiteQPochhammerIn_inv_base_reversal_units
      (Units.mk0 a ha) (Units.mk0 q hq) n

/-! ## The terminating specialization -/

/-- **Root-safe terminating numerator.**  For `k <= N`,

`prod_{j<k} (q^N - q^j) =
  (-1)^k q^(k choose 2) (q^(N-k+1);q)_k`.

No inverse, cancellation, or regularity hypothesis occurs, so the identity
holds in every commutative ring, at roots of unity, and with zero divisors. -/
theorem prod_pow_sub_pow_eq_finiteQPochhammerIn
    {R : Type*} [CommRing R] (q : R)
    {N k : ℕ} (hk : k ≤ N) :
    (∏ j ∈ Finset.range k, (q ^ N - q ^ j)) =
      (-1 : R) ^ k * q ^ k.choose 2 *
        finiteQPochhammerIn (q ^ (N - k + 1)) q k := by
  have hfactor (j : ℕ) (hj : j < k) :
      q ^ N - q ^ j = (-q ^ j) * (1 - q ^ (N - j)) := by
    have hjN : j ≤ N := (Nat.le_of_lt hj).trans hk
    have hpow : q ^ j * q ^ (N - j) = q ^ N := by
      rw [← pow_add, Nat.add_sub_of_le hjN]
    rw [mul_sub, mul_one]
    rw [show (-q ^ j) * q ^ (N - j) = -(q ^ j * q ^ (N - j)) by ring,
      hpow]
    ring
  have hprefactor :
      (∏ j ∈ Finset.range k, (-q ^ j)) =
        (-1 : R) ^ k * q ^ k.choose 2 := by
    calc
      (∏ j ∈ Finset.range k, (-q ^ j)) =
          ∏ j ∈ Finset.range k, (-1 : R) * q ^ j := by
        apply Finset.prod_congr rfl
        intro j _hj
        ring
      _ = (-1 : R) ^ k * q ^ k.choose 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_range, Finset.prod_pow_eq_pow_sum,
          Finset.sum_range_id, Nat.choose_two_right]
  have htail :
      (∏ j ∈ Finset.range k, (1 - q ^ (N - j))) =
        finiteQPochhammerIn (q ^ (N - k + 1)) q k := by
    unfold finiteQPochhammerIn
    rw [← Finset.prod_range_reflect
      (fun j => (1 - q ^ (N - k + 1) * q ^ j)) k]
    apply Finset.prod_congr rfl
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    rw [← pow_add]
    congr 2
    omega
  calc
    (∏ j ∈ Finset.range k, (q ^ N - q ^ j)) =
        ∏ j ∈ Finset.range k,
          ((-q ^ j) * (1 - q ^ (N - j))) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hfactor j (Finset.mem_range.mp hj)
    _ = (∏ j ∈ Finset.range k, (-q ^ j)) *
          ∏ j ∈ Finset.range k, (1 - q ^ (N - j)) := by
      rw [Finset.prod_mul_distrib]
    _ = (-1 : R) ^ k * q ^ k.choose 2 *
          finiteQPochhammerIn (q ^ (N - k + 1)) q k := by
      rw [hprefactor, htail]

/-- **Cleared terminating specialization.**  In a field, if `q != 0` and
`k <= N`, then

`q^(N*k) ((q^N)⁻¹;q)_k =
  (-1)^k q^(k choose 2) (q^(N-k+1);q)_k`.

This is the denominator-cleared form of the usual `q^(-N)` identity; its
right side is the root-safe polynomial numerator. -/
theorem pow_mul_finiteQPochhammerIn_inv_pow_eq
    {K : Type*} [Field K] (q : K) (hq : q ≠ 0)
    {N k : ℕ} (hk : k ≤ N) :
    q ^ (N * k) * finiteQPochhammerIn (q ^ N)⁻¹ q k =
      (-1 : K) ^ k * q ^ k.choose 2 *
        finiteQPochhammerIn (q ^ (N - k + 1)) q k := by
  have hqN : q ^ N ≠ 0 := pow_ne_zero N hq
  calc
    q ^ (N * k) * finiteQPochhammerIn (q ^ N)⁻¹ q k =
        (q ^ N) ^ k * finiteQPochhammerIn (q ^ N)⁻¹ q k := by
      rw [pow_mul]
    _ = (∏ _j ∈ Finset.range k, q ^ N) *
          ∏ j ∈ Finset.range k,
            (1 - (q ^ N)⁻¹ * q ^ j) := by
      rw [finiteQPochhammerIn, Finset.prod_const, Finset.card_range]
    _ = ∏ j ∈ Finset.range k,
          ((q ^ N) * (1 - (q ^ N)⁻¹ * q ^ j)) := by
      rw [Finset.prod_mul_distrib]
    _ = ∏ j ∈ Finset.range k, (q ^ N - q ^ j) := by
      apply Finset.prod_congr rfl
      intro j _hj
      rw [mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ hqN, one_mul]
    _ = (-1 : K) ^ k * q ^ k.choose 2 *
          finiteQPochhammerIn (q ^ (N - k + 1)) q k :=
      prod_pow_sub_pow_eq_finiteQPochhammerIn q hk

/-- **Terminating quotient formula.**  If `q != 0`, `k <= N`, and the
displayed q-Pochhammer denominator is nonzero, then

`((q^N)⁻¹;q)_k =
  ((-1)^k q^(k choose 2) (q;q)_N) /
    (q^(N*k) (q;q)_(N-k))`.

The assumptions are exactly those needed to divide the cleared identity;
no nonvanishing condition is imposed on the numerator. -/
theorem finiteQPochhammerIn_inv_pow_eq_self_div
    {K : Type*} [Field K] (q : K) (hq : q ≠ 0)
    {N k : ℕ} (hk : k ≤ N)
    (hden : finiteQPochhammerIn q q (N - k) ≠ 0) :
    finiteQPochhammerIn (q ^ N)⁻¹ q k =
      ((-1 : K) ^ k * q ^ k.choose 2 * finiteQPochhammerIn q q N) /
        (q ^ (N * k) * finiteQPochhammerIn q q (N - k)) := by
  have hclear := pow_mul_finiteQPochhammerIn_inv_pow_eq q hq hk
  have hsplit :
      finiteQPochhammerIn q q N =
        finiteQPochhammerIn q q (N - k) *
          finiteQPochhammerIn (q ^ (N - k + 1)) q k := by
    calc
      finiteQPochhammerIn q q N =
          finiteQPochhammerIn q q ((N - k) + k) := by
        rw [Nat.sub_add_cancel hk]
      _ = finiteQPochhammerIn q q (N - k) *
          finiteQPochhammerIn (q ^ (N - k + 1)) q k :=
        finiteQPochhammerIn_self_add q (N - k) k
  have hfull :
      q ^ (N * k) * finiteQPochhammerIn q q (N - k) ≠ 0 :=
    mul_ne_zero (pow_ne_zero (N * k) hq) hden
  apply (eq_div_iff hfull).2
  calc
    finiteQPochhammerIn (q ^ N)⁻¹ q k *
          (q ^ (N * k) * finiteQPochhammerIn q q (N - k)) =
        finiteQPochhammerIn q q (N - k) *
          (q ^ (N * k) * finiteQPochhammerIn (q ^ N)⁻¹ q k) := by
      ring
    _ = finiteQPochhammerIn q q (N - k) *
          ((-1 : K) ^ k * q ^ k.choose 2 *
            finiteQPochhammerIn (q ^ (N - k + 1)) q k) := by
      rw [hclear]
    _ = (-1 : K) ^ k * q ^ k.choose 2 *
          (finiteQPochhammerIn q q (N - k) *
            finiteQPochhammerIn (q ^ (N - k + 1)) q k) := by
      ring
    _ = (-1 : K) ^ k * q ^ k.choose 2 *
          finiteQPochhammerIn q q N := by
      rw [← hsplit]

/-- **Vanishing beyond the terminating index.**  If `q != 0` and `N < k`,
then `((q^N)⁻¹;q)_k = 0`: the factor indexed by `N` is exactly `1 - 1`.

This is the second clause of the terminating specialization and is kept
separate from the `k <= N` quotient formula. -/
theorem finiteQPochhammerIn_inv_pow_eq_zero_of_lt
    {K : Type*} [Field K] (q : K) (hq : q ≠ 0)
    {N k : ℕ} (hNk : N < k) :
    finiteQPochhammerIn (q ^ N)⁻¹ q k = 0 := by
  have hqN : q ^ N ≠ 0 := pow_ne_zero N hq
  unfold finiteQPochhammerIn
  apply Finset.prod_eq_zero (i := N)
  · exact Finset.mem_range.mpr hNk
  · rw [inv_mul_cancel₀ hqN, sub_self]

/-! ## First-column and adjacent Gaussian identities -/

/-- **The first Gaussian column with its natural denominator cleared.**
For every `n` over a commutative ring,

`(1-q) [n choose 1]_q = 1-q^n`.

The statement includes `n = 0` and remains valid when `1-q` vanishes or is a
zero divisor. -/
theorem one_sub_mul_gaussianBinomial_one
    {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    (1 - q) * gaussianBinomial q n 1 = 1 - q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [gaussianBinomial_succ_succ]
      simp only [Nat.sub_zero, gaussianBinomial_zero_right, mul_one]
      rw [mul_add, ih, pow_succ]
      ring

/-- **Adjacent-column cross identity.**  For `k < n`,

`(1-q^(k+1)) [n choose k+1]_q =
  (1-q^(n-k)) [n choose k]_q`.

This denominator-free identity holds over every commutative ring, including
at roots of unity. -/
private theorem gaussianBinomial_adjacent_mul_of_lt
    {R : Type*} [CommRing R] (q : R)
    {n k : ℕ} (hk : k < n) :
    (1 - q ^ (k + 1)) * gaussianBinomial q n (k + 1) =
      (1 - q ^ (n - k)) * gaussianBinomial q n k := by
  have hsymm :
      gaussianBinomial q (k + 1) k =
        gaussianBinomial q (k + 1) 1 := by
    simpa using
      (gaussianBinomial_symm q (n := k + 1) (k := k)
        (Nat.le_succ k)).symm
  have hflag :=
    gaussianBinomial_mul q (n := n) (k := k + 1) (j := k)
      (Nat.le_succ k) (Nat.succ_le_iff.mpr hk)
  rw [hsymm] at hflag
  have hflag' :
      gaussianBinomial q n (k + 1) *
          gaussianBinomial q (k + 1) 1 =
        gaussianBinomial q n k * gaussianBinomial q (n - k) 1 := by
    simpa only [Nat.add_sub_cancel_left] using hflag
  calc
    (1 - q ^ (k + 1)) * gaussianBinomial q n (k + 1) =
        ((1 - q) * gaussianBinomial q (k + 1) 1) *
          gaussianBinomial q n (k + 1) := by
      rw [one_sub_mul_gaussianBinomial_one]
    _ = (1 - q) *
          (gaussianBinomial q n (k + 1) *
            gaussianBinomial q (k + 1) 1) := by
      ring
    _ = (1 - q) *
          (gaussianBinomial q n k *
            gaussianBinomial q (n - k) 1) := by
      rw [hflag']
    _ = ((1 - q) * gaussianBinomial q (n - k) 1) *
          gaussianBinomial q n k := by
      ring
    _ = (1 - q ^ (n - k)) * gaussianBinomial q n k := by
      rw [one_sub_mul_gaussianBinomial_one]

/-- **Total adjacent-column cross identity.**  For all natural `n` and `k`,

`(1-q^(k+1)) [n choose k+1]_q =
  (1-q^(n-k)) [n choose k]_q`.

On the natural triangle this is the denominator-free form of the adjacent
ratio.  On and above its boundary, zero extension makes both sides vanish.
The identity therefore remains valid at roots of unity without any index or
nonvanishing hypothesis. -/
theorem gaussianBinomial_adjacent_mul
    {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    (1 - q ^ (k + 1)) * gaussianBinomial q n (k + 1) =
      (1 - q ^ (n - k)) * gaussianBinomial q n k := by
  by_cases hk : k < n
  · exact gaussianBinomial_adjacent_mul_of_lt q hk
  · have hnk : n ≤ k := Nat.le_of_not_gt hk
    rcases hnk.eq_or_lt with rfl | hnk
    · rw [gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
      simp
    · rw [gaussianBinomial_eq_zero_of_lt q hnk,
        gaussianBinomial_eq_zero_of_lt q (by omega : n < k + 1)]
      simp

/-- **Adjacent-row cross identity.**  For `k < n`,

`(1-q^(n-k)) [n choose k]_q =
  (1-q^n) [n-1 choose k]_q`.

Unlike the associated quotient, this polynomial identity remains valid at
roots of unity and requires no nonvanishing hypothesis. -/
private theorem gaussianBinomial_row_adjacent_mul_of_lt
    {R : Type*} [CommRing R] (q : R)
    {n k : ℕ} (hk : k < n) :
    (1 - q ^ (n - k)) * gaussianBinomial q n k =
      (1 - q ^ n) * gaussianBinomial q (n - 1) k := by
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  have hleft :
      gaussianBinomial q n (n - 1) = gaussianBinomial q n 1 := by
    have h :=
      (gaussianBinomial_symm q (n := n) (k := n - 1)
        (Nat.sub_le n 1)).symm
    simpa only [show n - (n - 1) = 1 by omega] using h
  have hright :
      gaussianBinomial q (n - k) (n - 1 - k) =
        gaussianBinomial q (n - k) 1 := by
    have h :=
      (gaussianBinomial_symm q (n := n - k) (k := n - 1 - k)
        (by omega)).symm
    simpa only [show n - k - (n - 1 - k) = 1 by omega] using h
  have hflag :=
    gaussianBinomial_mul q (n := n) (k := n - 1) (j := k)
      (by omega) (Nat.sub_le n 1)
  rw [hleft, hright] at hflag
  calc
    (1 - q ^ (n - k)) * gaussianBinomial q n k =
        ((1 - q) * gaussianBinomial q (n - k) 1) *
          gaussianBinomial q n k := by
      rw [one_sub_mul_gaussianBinomial_one]
    _ = (1 - q) *
          (gaussianBinomial q n k *
            gaussianBinomial q (n - k) 1) := by
      ring
    _ = (1 - q) *
          (gaussianBinomial q n 1 *
            gaussianBinomial q (n - 1) k) := by
      rw [← hflag]
    _ = ((1 - q) * gaussianBinomial q n 1) *
          gaussianBinomial q (n - 1) k := by
      ring
    _ = (1 - q ^ n) * gaussianBinomial q (n - 1) k := by
      rw [one_sub_mul_gaussianBinomial_one]

/-- **Total adjacent-row cross identity.**  For all natural `n` and `k`,

`(1-q^(n-k)) [n choose k]_q =
  (1-q^n) [n-1 choose k]_q`.

Below the row boundary this clears the adjacent-row quotient.  At and above
the boundary both sides vanish by zero extension, so the result is total and
requires no nonvanishing or regularity hypothesis. -/
theorem gaussianBinomial_row_adjacent_mul
    {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    (1 - q ^ (n - k)) * gaussianBinomial q n k =
      (1 - q ^ n) * gaussianBinomial q (n - 1) k := by
  by_cases hk : k < n
  · exact gaussianBinomial_row_adjacent_mul_of_lt q hk
  · have hnk : n ≤ k := Nat.le_of_not_gt hk
    rcases hnk.eq_or_lt with rfl | hnk
    · cases n with
      | zero => simp
      | succ n =>
          rw [gaussianBinomial_eq_zero_of_lt q (by omega : n + 1 - 1 < n + 1)]
          simp
    · rw [gaussianBinomial_eq_zero_of_lt q hnk,
        gaussianBinomial_eq_zero_of_lt q (by omega : n - 1 < k)]
      simp

/-- **Adjacent-column quotient.**  Over a field, if both displayed
denominators are nonzero and `k < n`, then

`[n choose k+1]_q / [n choose k]_q =
  (1-q^(n-k)) / (1-q^(k+1))`.

The assumptions are precisely the two denominator conditions; the root-safe
cross identity above is available without them. -/
theorem gaussianBinomial_adjacent_div
    {K : Type*} [Field K] (q : K)
    {n k : ℕ} (_hk : k < n)
    (hbin : gaussianBinomial q n k ≠ 0)
    (hfactor : 1 - q ^ (k + 1) ≠ 0) :
    gaussianBinomial q n (k + 1) / gaussianBinomial q n k =
      (1 - q ^ (n - k)) / (1 - q ^ (k + 1)) := by
  apply (div_eq_div_iff hbin hfactor).2
  simpa only [mul_comm] using gaussianBinomial_adjacent_mul q n k

/-- **Adjacent-row quotient.**  Over a field, if both displayed
denominators are nonzero and `k < n`, then

`[n choose k]_q / [n-1 choose k]_q =
  (1-q^n) / (1-q^(n-k))`.

The assumptions are exactly the two denominator conditions suppressed in
the informal ratio notation. -/
theorem gaussianBinomial_row_adjacent_div
    {K : Type*} [Field K] (q : K)
    {n k : ℕ} (_hk : k < n)
    (hbin : gaussianBinomial q (n - 1) k ≠ 0)
    (hfactor : 1 - q ^ (n - k) ≠ 0) :
    gaussianBinomial q n k / gaussianBinomial q (n - 1) k =
      (1 - q ^ n) / (1 - q ^ (n - k)) := by
  apply (div_eq_div_iff hbin hfactor).2
  simpa only [mul_comm] using gaussianBinomial_row_adjacent_mul q n k

end Fabius
