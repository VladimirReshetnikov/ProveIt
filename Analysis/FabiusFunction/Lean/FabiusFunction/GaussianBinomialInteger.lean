import FabiusFunction.QPochhammerElementaryIdentities
import FabiusFunction.QBinomialTheoremInfinite
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Gaussian coefficients with an integer upper index

For `N ∈ ℤ` and `k ∈ ℕ` the **generalized Gaussian coefficient** is

`[N,k]_q = (q^{N-k+1};q)_k / (q;q)_k`,

which agrees with `gaussianBinomial` for `N ≥ 0` (including the value `0` for `k > N`) and
satisfies both `q`-Pascal recurrences for every integer `N`.  The **negative-index
reflection**

`[-m,k]_q = (-1)^k q^{-mk - C(k,2)} [m+k-1,k]_q`

is base reversal of the numerator, `(q^{-(m+k-1)};q)_k = (-1)^k q^{-k(m+k-1)+C(k,2)} (q^m;q)_k`,
followed by the identity `(q^m;q)_k/(q;q)_k = [m+k-1,k]_q`, valid for all `m, k`.
The latter identity also turns Euler's infinite `q`-binomial theorem at `a = q^m` into the
**reciprocal finite `q`-binomial series**

`1/(z;q)_m = ∑_k [m+k-1,k]_q z^k = ∑_k (-1)^k q^{mk+C(k,2)} [-m,k]_q z^k`  (`‖z‖ < 1`).

## Main declarations

* `finiteQPochhammerIn_inv_base_eq`, `finiteQPochhammerIn_mul_pow_inv_base`: index reflection
  `(b;q⁻¹)_k = (b q^{-(k-1)};q)_k`.
* `gaussianBinomialZ`, `gaussianBinomialZ_natCast`, `gaussianBinomialZ_succ`,
  `gaussianBinomialZ_succ'`: the definition, agreement, and the two Pascal laws.
* `finiteQPochhammerIn_pow_div`: `(q^m;q)_k/(q;q)_k = [m+k-1,k]_q`.
* `gaussianBinomialZ_neg_natCast`: the negative-index reflection.
* `hasSum_reciprocal_finiteQPochhammerIn`, `hasSum_reciprocal_finiteQPochhammerIn_neg`:
  the reciprocal series in both forms.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

section Field

variable {K : Type*} [Field K] {q : K}

/-- Index reflection of a finite symbol with inverted base: `(b;q⁻¹)_k = (b q^{-(k-1)};q)_k`. -/
theorem finiteQPochhammerIn_inv_base_eq (hq0 : q ≠ 0) (b : K) (k : ℕ) :
    finiteQPochhammerIn b q⁻¹ k = finiteQPochhammerIn (b * q⁻¹ ^ (k - 1)) q k := by
  unfold finiteQPochhammerIn
  rw [← prod_range_reflect (fun j => 1 - b * q⁻¹ ^ j) k]
  refine prod_congr rfl fun i hi => ?_
  have hi' : i < k := mem_range.mp hi
  congr 1
  have hsplit : q⁻¹ ^ (k - 1) = q⁻¹ ^ (k - 1 - i) * q⁻¹ ^ i := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : i ≤ k - 1)]
  rw [hsplit, mul_assoc, mul_assoc, ← mul_pow, inv_mul_cancel₀ hq0, one_pow, mul_one]

/-- Index reflection, second form: `(b q^{k-1};q⁻¹)_k = (b;q)_k`. -/
theorem finiteQPochhammerIn_mul_pow_inv_base (hq0 : q ≠ 0) (b : K) (k : ℕ) :
    finiteQPochhammerIn (b * q ^ (k - 1)) q⁻¹ k = finiteQPochhammerIn b q k := by
  rw [finiteQPochhammerIn_inv_base_eq hq0, mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0, one_pow,
    mul_one]

/-- `(q^m;q)_k / (q;q)_k = [m+k-1,k]_q` for all `m` and `k` (the case `m = 0`, `k ≥ 1` reads
`0 = 0`). -/
theorem finiteQPochhammerIn_pow_div (q : K) (m k : ℕ) (hk : finiteQPochhammerIn q q k ≠ 0) :
    finiteQPochhammerIn (q ^ m) q k / finiteQPochhammerIn q q k =
      gaussianBinomial q (m + k - 1) k := by
  rcases k with _ | k
  · simp [gaussianBinomial_zero_right]
  rcases m with _ | m
  · rw [pow_zero, finiteQPochhammerIn_succ_shift 1 q k, sub_self, zero_mul, zero_div,
      show 0 + (k + 1) - 1 = k by omega, gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self k)]
  · have hG := finiteQPochhammerIn_self_mul_gaussianBinomial q
      (show k + 1 ≤ m + 1 + (k + 1) - 1 by omega)
    rw [show m + 1 + (k + 1) - 1 - (k + 1) + 1 = m + 1 by omega] at hG
    rw [← hG, mul_div_cancel_left₀ _ hk]

/-- **The Gaussian coefficient with integer upper index** `[N,k]_q = (q^{N-k+1};q)_k/(q;q)_k`. -/
noncomputable def gaussianBinomialZ (q : K) (N : ℤ) (k : ℕ) : K :=
  finiteQPochhammerIn (q ^ (N - k + 1)) q k / finiteQPochhammerIn q q k

/-- `[N,0]_q = 1`. -/
@[simp] theorem gaussianBinomialZ_zero_right (q : K) (N : ℤ) : gaussianBinomialZ q N 0 = 1 := by
  simp [gaussianBinomialZ]

/-- For a natural upper index the generalized coefficient is the Gaussian coefficient,
including the value `0` above the diagonal. -/
theorem gaussianBinomialZ_natCast (hq0 : q ≠ 0) (n k : ℕ) (hk : finiteQPochhammerIn q q k ≠ 0) :
    gaussianBinomialZ q n k = gaussianBinomial q n k := by
  unfold gaussianBinomialZ
  rcases le_or_gt k n with h | h
  · rw [show ((n : ℤ) - k + 1) = ((n - k + 1 : ℕ) : ℤ) by omega, zpow_natCast,
      ← finiteQPochhammerIn_self_mul_gaussianBinomial q h, mul_div_cancel_left₀ _ hk]
  · rw [gaussianBinomial_eq_zero_of_lt q h, div_eq_zero_iff]
    left
    unfold finiteQPochhammerIn
    refine prod_eq_zero (i := k - n - 1) (mem_range.mpr (by omega)) ?_
    rw [← zpow_natCast, ← zpow_add₀ hq0,
      show ((n : ℤ) - k + 1 + ((k - n - 1 : ℕ) : ℤ)) = 0 by omega, zpow_zero, sub_self]

/-- **The first `q`-Pascal law for every integer upper index**:
`[N,k+1]_q = [N-1,k]_q + q^{k+1} [N-1,k+1]_q`. -/
theorem gaussianBinomialZ_succ (hq0 : q ≠ 0) (N : ℤ) (k : ℕ)
    (hk : finiteQPochhammerIn q q (k + 1) ≠ 0) :
    gaussianBinomialZ q N (k + 1) =
      gaussianBinomialZ q (N - 1) k + q ^ (k + 1) * gaussianBinomialZ q (N - 1) (k + 1) := by
  have hA : finiteQPochhammerIn q q k ≠ 0 := by
    intro h; rw [finiteQPochhammerIn_succ, h, zero_mul] at hk; exact hk rfl
  have hB : 1 - q * q ^ k ≠ 0 := by
    intro h; rw [finiteQPochhammerIn_succ, h, mul_zero] at hk; exact hk rfl
  unfold gaussianBinomialZ
  have e1 : N - ((k + 1 : ℕ) : ℤ) + 1 = N - k := by push_cast; ring
  have e2 : N - 1 - (k : ℤ) + 1 = N - k := by ring
  have e3 : N - 1 - ((k + 1 : ℕ) : ℤ) + 1 = N - k - 1 := by push_cast; ring
  rw [e1, e2, e3, finiteQPochhammerIn_succ (q ^ (N - k)) q k,
    finiteQPochhammerIn_succ_shift (q ^ (N - k - 1)) q k, zpow_sub_one₀ hq0,
    inv_mul_cancel_right₀ hq0, finiteQPochhammerIn_succ q q k]
  set B := 1 - q * q ^ k with hBdef
  field_simp
  rw [hBdef]
  ring

/-- **The second `q`-Pascal law for every integer upper index**:
`[N,k+1]_q = q^{N-k-1} [N-1,k]_q + [N-1,k+1]_q`. -/
theorem gaussianBinomialZ_succ' (hq0 : q ≠ 0) (N : ℤ) (k : ℕ)
    (hk : finiteQPochhammerIn q q (k + 1) ≠ 0) :
    gaussianBinomialZ q N (k + 1) =
      q ^ (N - (k + 1 : ℕ)) * gaussianBinomialZ q (N - 1) k +
        gaussianBinomialZ q (N - 1) (k + 1) := by
  have hA : finiteQPochhammerIn q q k ≠ 0 := by
    intro h; rw [finiteQPochhammerIn_succ, h, zero_mul] at hk; exact hk rfl
  have hB : 1 - q * q ^ k ≠ 0 := by
    intro h; rw [finiteQPochhammerIn_succ, h, mul_zero] at hk; exact hk rfl
  unfold gaussianBinomialZ
  have e1 : N - ((k + 1 : ℕ) : ℤ) + 1 = N - k := by push_cast; ring
  have e2 : N - 1 - (k : ℤ) + 1 = N - k := by ring
  have e3 : N - 1 - ((k + 1 : ℕ) : ℤ) + 1 = N - k - 1 := by push_cast; ring
  have e4 : N - ((k + 1 : ℕ) : ℤ) = N - k - 1 := by push_cast; ring
  rw [e1, e2, e3, e4, finiteQPochhammerIn_succ (q ^ (N - k)) q k,
    finiteQPochhammerIn_succ_shift (q ^ (N - k - 1)) q k, zpow_sub_one₀ hq0,
    inv_mul_cancel_right₀ hq0, finiteQPochhammerIn_succ q q k]
  set B := 1 - q * q ^ k with hBdef
  field_simp
  rw [hBdef]
  ring

/-- **Negative-index reflection**: `[-m,k]_q = (-1)^k q^{-(mk + C(k,2))} [m+k-1,k]_q`, for all
`m, k ∈ ℕ`. -/
theorem gaussianBinomialZ_neg_natCast (hq0 : q ≠ 0) (m k : ℕ)
    (hk : finiteQPochhammerIn q q k ≠ 0) :
    gaussianBinomialZ q (-(m : ℤ)) k =
      (-1) ^ k * (q ^ (m * k + k.choose 2))⁻¹ * gaussianBinomial q (m + k - 1) k := by
  rcases k with _ | k
  · simp [gaussianBinomial_zero_right]
  unfold gaussianBinomialZ
  have hb : (-(m : ℤ) - ((k + 1 : ℕ) : ℤ) + 1) = -((m + k : ℕ) : ℤ) := by push_cast; ring
  have hrefl : finiteQPochhammerIn (q ^ (m + k)) q⁻¹ (k + 1) =
      finiteQPochhammerIn (q ^ m) q (k + 1) := by
    rw [← finiteQPochhammerIn_mul_pow_inv_base hq0 (q ^ m) (k + 1), Nat.add_sub_cancel, pow_add]
  have hC2 : (k + 1).choose 2 * 2 = (k + 1) * k := by
    rw [Nat.choose_two_right,
      Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self (k + 1))),
      Nat.add_sub_cancel]
  have hexp : (q ^ (m + k)) ^ (k + 1) =
      q ^ (m * (k + 1) + (k + 1).choose 2) * q ^ ((k + 1).choose 2) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    linarith [hC2]
  have hpref : (-(q ^ (m + k))⁻¹) ^ (k + 1) * q ^ (k + 1).choose 2 =
      (-1) ^ (k + 1) * (q ^ (m * (k + 1) + (k + 1).choose 2))⁻¹ := by
    rw [neg_pow, inv_pow, hexp, mul_inv, mul_assoc, inv_mul_cancel_right₀ (pow_ne_zero _ hq0)]
  rw [hb, zpow_neg, zpow_natCast,
    finiteQPochhammerIn_base_reversal _ q (inv_ne_zero (pow_ne_zero _ hq0)) hq0, inv_inv, hrefl,
    mul_div_assoc, finiteQPochhammerIn_pow_div q m (k + 1) hk, hpref]

end Field

section Analytic

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {q z : 𝕜}

/-- **The reciprocal finite `q`-binomial series**: `1/(z;q)_m = ∑_k [m+k-1,k]_q z^k` for
`‖q‖ < 1`, `‖z‖ < 1`, and every `m` (for `m = 0` only the constant term survives). -/
theorem hasSum_reciprocal_finiteQPochhammerIn (hq : ‖q‖ < 1) (m : ℕ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => gaussianBinomial q (m + k - 1) k * z ^ k)
      (finiteQPochhammerIn z q m)⁻¹ := by
  have h := hasSum_qBinomial_theorem hq (q ^ m) hz
  have hzq : ‖z * q ^ m‖ < 1 := by
    rw [norm_mul, norm_pow]
    calc ‖z‖ * ‖q‖ ^ m ≤ ‖z‖ * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg q) hq.le
      _ < 1 := by rw [mul_one]; exact hz
  have hne : qPochhammerInfIn (z * q ^ m) q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hzq
  have hval : qPochhammerInfIn (q ^ m * z) q / qPochhammerInfIn z q =
      (finiteQPochhammerIn z q m)⁻¹ := by
    rw [mul_comm, qPochhammerInfIn_eq_finite_mul_shift z hq m, div_mul_cancel_right₀ hne]
  have hterm : (fun k : ℕ => finiteQPochhammerIn (q ^ m) q k / finiteQPochhammerIn q q k * z ^ k) =
      fun k : ℕ => gaussianBinomial q (m + k - 1) k * z ^ k :=
    funext fun k => by
      rw [finiteQPochhammerIn_pow_div q m k (finiteQPochhammerIn_self_ne_zero hq k)]
  rw [hterm, hval] at h
  exact h

/-- The reciprocal series written with negative upper indices:
`1/(z;q)_m = ∑_k (-1)^k q^{mk + C(k,2)} [-m,k]_q z^k`. -/
theorem hasSum_reciprocal_finiteQPochhammerIn_neg (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (m : ℕ)
    (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ =>
        (-1) ^ k * q ^ (m * k + k.choose 2) * gaussianBinomialZ q (-(m : ℤ)) k * z ^ k)
      (finiteQPochhammerIn z q m)⁻¹ := by
  have h := hasSum_reciprocal_finiteQPochhammerIn hq m hz
  have hterm : (fun k : ℕ => gaussianBinomial q (m + k - 1) k * z ^ k) =
      fun k : ℕ =>
        (-1) ^ k * q ^ (m * k + k.choose 2) * gaussianBinomialZ q (-(m : ℤ)) k * z ^ k :=
    funext fun k => by
      rw [gaussianBinomialZ_neg_natCast hq0 m k (finiteQPochhammerIn_self_ne_zero hq k)]
      have h1 : ((-1 : 𝕜) ^ k) * (-1) ^ k = 1 := by
        rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
      have h2 : q ^ (m * k + k.choose 2) * (q ^ (m * k + k.choose 2))⁻¹ = 1 :=
        mul_inv_cancel₀ (pow_ne_zero _ hq0)
      rw [show (-1 : 𝕜) ^ k * q ^ (m * k + k.choose 2) *
          ((-1) ^ k * (q ^ (m * k + k.choose 2))⁻¹ * gaussianBinomial q (m + k - 1) k) =
          ((-1) ^ k * (-1) ^ k) * (q ^ (m * k + k.choose 2) * (q ^ (m * k + k.choose 2))⁻¹) *
            gaussianBinomial q (m + k - 1) k by ring, h1, h2, one_mul, one_mul]
  rw [hterm] at h
  exact h

end Analytic

end Fabius
