import FabiusFunction.GaussianBinomialPalindromic
import FabiusFunction.GaussianBinomialContinuity
import FabiusFunction.GaussianBinomialUniversal
import FabiusFunction.GeneralQConditionNumber
import FabiusFunction.QBinomialReciprocity
import FabiusFunction.QBinomialTheoremInfinite

/-!
# Gaussian coefficients at `q > 1`: reciprocity and dimension-dominant bounds

The **reciprocity** `[n,k]_q = q^{k(n-k)} [n,k]_{q⁻¹}` (`q ≠ 0`), proved
division-free over units in `QBinomialReciprocity`, transfers everything
known for `0 ≤ q < 1` to `q > 1`.  For `0 ≤ q < 1` the coefficient lies
between its constant term `1` and `1/(q;q)_∞`:

`1 ≤ [n,k]_q ≤ 1/(q;q)_k ≤ 1/(q;q)_∞`,

the first because all coefficients of the universal polynomial are nonnegative and the
constant one is `1`, the second because `[n,k]_q = (q^{n-k+1};q)_k/(q;q)_k` with a
numerator at most `1`.  Hence for `Q > 1`

`Q^{k(n-k)} ≤ [n,k]_Q ≤ Q^{k(n-k)} / (Q⁻¹;Q⁻¹)_∞`.

## Main declarations

* `gaussianBinomial_inv`: reciprocity in any field.
* `one_le_gaussianBinomial`: `1 ≤ [n,k]_q` for `q ≥ 0` in any ordered field.
* `gaussianBinomial_le_inv_qPochhammerInfIn`: `[n,k]_q ≤ 1/(q;q)_∞` for `0 ≤ q < 1`.
* `pow_le_gaussianBinomial_of_one_lt`, `gaussianBinomial_le_pow_div_of_one_lt`: the bounds at
  `Q > 1`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial

section Field

variable {K : Type*} [Field K]

/-- **Reciprocity** `[n,k]_q = q^{k(n-k)} [n,k]_{q⁻¹}` for `q ≠ 0`, the
evaluated form of palindromicity.  This is `gaussianBinomial_reciprocity`
read from right to left; the hypothesis `k ≤ n` is not needed (both sides
vanish above the diagonal) and is kept only for the signature. -/
theorem gaussianBinomial_inv (q : K) (hq0 : q ≠ 0) {n k : ℕ}
    (_hk : k ≤ n) :
    gaussianBinomial q n k =
      q ^ (k * (n - k)) * gaussianBinomial q⁻¹ n k :=
  (gaussianBinomial_reciprocity q hq0 n k).symm

end Field

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `1 ≤ [n,k]_q` for `q ≥ 0` and `k ≤ n`: the universal polynomial has nonnegative
coefficients and constant term `1`. -/
theorem one_le_gaussianBinomial {q : K} (hq : 0 ≤ q) {n k : ℕ} (hk : k ≤ n) :
    1 ≤ gaussianBinomial q n k := by
  rw [gaussianBinomial_eq_eval₂_universal, eval₂_eq_sum_range]
  have h0 : (0 : ℕ) ∈ Finset.range ((gaussianBinomial (X : ℕ[X]) n k).natDegree + 1) :=
    Finset.mem_range.mpr (Nat.succ_pos _)
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => ?_) h0)
  · rw [coeff_gaussianBinomial_zero hk]
    simp
  · exact mul_nonneg (by simp) (pow_nonneg hq i)

end Ordered

section Real

/-- `(q^m;q)_k ≤ 1` for `0 ≤ q ≤ 1`. -/
theorem finiteQPochhammerIn_pow_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m k : ℕ) :
    finiteQPochhammerIn (q ^ m) q k ≤ 1 := by
  unfold finiteQPochhammerIn
  refine Finset.prod_le_one (fun j _ => ?_) fun j _ => ?_
  · have h : q ^ m * q ^ j ≤ 1 := by
      rw [← pow_add]
      exact pow_le_one₀ hq0 hq1
    linarith
  · have h : 0 ≤ q ^ m * q ^ j := by positivity
    linarith

/-- **Upper bound** `[n,k]_q ≤ 1/(q;q)_∞` for `0 ≤ q < 1`, `k ≤ n`. -/
theorem gaussianBinomial_le_inv_qPochhammerInfIn {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {n k : ℕ}
    (hk : k ≤ n) : gaussianBinomial q n k ≤ (qPochhammerInfIn q q)⁻¹ := by
  have hk0 : 0 < finiteQPochhammerIn q q k := finiteQPochhammerIn_self_pos hq0 hq1 k
  have hinf : 0 < qPochhammerInfIn q q := qPochhammerInfIn_pos_of_lt_one hq0 hq1 hq0 hq1
  have hle : qPochhammerInfIn q q ≤ finiteQPochhammerIn q q k :=
    qPochhammerInfIn_le_finiteQPochhammerIn hq0 hq1.le hq0 hq1 k
  rw [gaussianBinomial_eq_finiteQPochhammerIn_div hk hk0.ne', div_le_iff₀ hk0]
  calc finiteQPochhammerIn (q ^ (n - k + 1)) q k ≤ 1 :=
        finiteQPochhammerIn_pow_le_one hq0 hq1.le _ k
    _ = (qPochhammerInfIn q q)⁻¹ * qPochhammerInfIn q q := (inv_mul_cancel₀ hinf.ne').symm
    _ ≤ (qPochhammerInfIn q q)⁻¹ * finiteQPochhammerIn q q k :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hinf.le)

/-- **Dimension-dominant lower bound**: `Q^{k(n-k)} ≤ [n,k]_Q` for `Q > 1`. -/
theorem pow_le_gaussianBinomial_of_one_lt {Q : ℝ} (hQ : 1 < Q) {n k : ℕ} (hk : k ≤ n) :
    Q ^ (k * (n - k)) ≤ gaussianBinomial Q n k := by
  have hQ0 : 0 < Q := by linarith
  rw [gaussianBinomial_inv Q hQ0.ne' hk]
  exact le_mul_of_one_le_right (pow_nonneg hQ0.le _)
    (one_le_gaussianBinomial (inv_nonneg.mpr hQ0.le) hk)

/-- **Dimension-dominant upper bound**: `[n,k]_Q ≤ Q^{k(n-k)} / (Q⁻¹;Q⁻¹)_∞` for `Q > 1`. -/
theorem gaussianBinomial_le_pow_div_of_one_lt {Q : ℝ} (hQ : 1 < Q) {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial Q n k ≤ Q ^ (k * (n - k)) / qPochhammerInfIn Q⁻¹ Q⁻¹ := by
  have hQ0 : 0 < Q := by linarith
  have hq0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr hQ0.le
  have hq1 : Q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hQ
  rw [gaussianBinomial_inv Q hQ0.ne' hk, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (gaussianBinomial_le_inv_qPochhammerInfIn hq0 hq1 hk)
    (pow_nonneg hQ0.le _)

end Real

end Fabius
