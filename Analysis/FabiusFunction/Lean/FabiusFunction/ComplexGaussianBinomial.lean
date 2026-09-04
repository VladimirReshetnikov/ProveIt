import FabiusFunction.GaussianBinomialComplexOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Gaussian coefficients with two complex arguments

For real `0 < q < 1` and complex `α, β`, with `q^z = exp(z log q)` (real logarithm), the
**two-argument Gaussian coefficient** is

`[α,β]_q = (q^{β+1};q)_∞ (q^{α-β+1};q)_∞ / ((q;q)_∞ (q^{α+1};q)_∞)`,

and the complex `q`-gamma function is `Γ_q(z) = (q;q)_∞ (1-q)^{1-z} / (q^z;q)_∞`.  The gamma
representation `[α,β]_q = Γ_q(α+1)/(Γ_q(β+1) Γ_q(α-β+1))` is immediate (all powers of `1-q`
cancel); the symmetry `[α,β]_q = [α,α-β]_q` is a relabelling; both Pascal laws
`[α+1,β]_q = q^β [α,β]_q + [α,β-1]_q = [α,β]_q + q^{α+1-β} [α,β-1]_q` follow from one shift of
each infinite symbol and `q^β q^{α-β+1} = q^{α+1}`; and at a natural `β = k` tail cancellation
recovers `[α,k]_q = (q^{α-k+1};q)_k/(q;q)_k`.

## Main declarations

* `qGammaC`, `gaussianBinomialCC`.
* `gaussianBinomialCC_eq_qGammaC`, `gaussianBinomialCC_symm`, `gaussianBinomialCC_succ_left`,
  `gaussianBinomialCC_succ_left'`, `gaussianBinomialCC_natCast`.
-/

set_option autoImplicit false

namespace Fabius

/-- The complex `q`-gamma function `Γ_q(z) = (q;q)_∞ (1-q)^{1-z}/(q^z;q)_∞` for real `q`. -/
noncomputable def qGammaC (q : ℝ) (z : ℂ) : ℂ :=
  qPochhammerInfIn (q : ℂ) q * (1 - (q : ℂ)) ^ (1 - z) / qPochhammerInfIn ((q : ℂ) ^ z) q

/-- **The Gaussian coefficient with two complex arguments**
`[α,β]_q = (q^{β+1};q)_∞ (q^{α-β+1};q)_∞ / ((q;q)_∞ (q^{α+1};q)_∞)`. -/
noncomputable def gaussianBinomialCC (q : ℝ) (α β : ℂ) : ℂ :=
  qPochhammerInfIn ((q : ℂ) ^ (β + 1)) q * qPochhammerInfIn ((q : ℂ) ^ (α - β + 1)) q /
    (qPochhammerInfIn (q : ℂ) q * qPochhammerInfIn ((q : ℂ) ^ (α + 1)) q)

variable {q : ℝ}

/-- `‖(q : ℂ)‖ < 1` for `0 < q < 1`. -/
theorem norm_ofReal_lt_one (hq0 : 0 < q) (hq1 : q < 1) : ‖(q : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg hq0.le]
  exact hq1

/-- `(q;q)_∞ ≠ 0` in `ℂ` for `0 < q < 1`. -/
theorem qPochhammerInfIn_ofReal_self_ne_zero (hq0 : 0 < q) (hq1 : q < 1) :
    qPochhammerInfIn (q : ℂ) q ≠ 0 := by
  refine qPochhammerInfIn_ne_zero _ (norm_ofReal_lt_one hq0 hq1) fun j h => ?_
  have h' : q * q ^ j = 1 := by exact_mod_cast h
  have hle : q * q ^ j ≤ q := mul_le_of_le_one_right hq0.le (pow_le_one₀ hq0.le hq1.le)
  linarith

/-- **Gamma representation** `[α,β]_q = Γ_q(α+1)/(Γ_q(β+1) Γ_q(α-β+1))`. -/
theorem gaussianBinomialCC_eq_qGammaC (hq0 : 0 < q) (hq1 : q < 1) {α β : ℂ}
    (hα : qPochhammerInfIn ((q : ℂ) ^ (α + 1)) q ≠ 0)
    (hβ : qPochhammerInfIn ((q : ℂ) ^ (β + 1)) q ≠ 0)
    (hαβ : qPochhammerInfIn ((q : ℂ) ^ (α - β + 1)) q ≠ 0) :
    gaussianBinomialCC q α β = qGammaC q (α + 1) / (qGammaC q (β + 1) * qGammaC q (α - β + 1)) := by
  have hP0 := qPochhammerInfIn_ofReal_self_ne_zero hq0 hq1
  have hb0 : (1 - (q : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hq1.ne')
  have hA : (1 - (q : ℂ)) ^ (1 - (α + 1)) = ((1 - (q : ℂ)) ^ α)⁻¹ := by
    rw [show (1 - (α + 1) : ℂ) = -α by ring, Complex.cpow_neg]
  have hB : (1 - (q : ℂ)) ^ (1 - (β + 1)) = ((1 - (q : ℂ)) ^ β)⁻¹ := by
    rw [show (1 - (β + 1) : ℂ) = -β by ring, Complex.cpow_neg]
  have hC : (1 - (q : ℂ)) ^ (1 - (α - β + 1)) = (1 - (q : ℂ)) ^ β * ((1 - (q : ℂ)) ^ α)⁻¹ := by
    rw [show (1 - (α - β + 1) : ℂ) = β + -α by ring, Complex.cpow_add _ _ hb0, Complex.cpow_neg]
  have hA0 : (1 - (q : ℂ)) ^ α ≠ 0 := fun h => hb0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hB0 : (1 - (q : ℂ)) ^ β ≠ 0 := fun h => hb0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  unfold gaussianBinomialCC qGammaC
  rw [hA, hB, hC]
  field_simp
  all_goals ring

/-- **Symmetry** `[α,β]_q = [α,α-β]_q`. -/
theorem gaussianBinomialCC_symm (q : ℝ) (α β : ℂ) :
    gaussianBinomialCC q α (α - β) = gaussianBinomialCC q α β := by
  unfold gaussianBinomialCC
  rw [show (α - (α - β) + 1 : ℂ) = β + 1 by ring, mul_comm]

/-- **First Pascal law** `[α+1,β]_q = q^β [α,β]_q + [α,β-1]_q`, whenever `(q^{α+1};q)_∞ ≠ 0`. -/
theorem gaussianBinomialCC_succ_left (hq0 : 0 < q) (hq1 : q < 1) {α β : ℂ}
    (hα : qPochhammerInfIn ((q : ℂ) ^ (α + 1)) q ≠ 0) :
    gaussianBinomialCC q (α + 1) β =
      (q : ℂ) ^ β * gaussianBinomialCC q α β + gaussianBinomialCC q α (β - 1) := by
  have hq := norm_ofReal_lt_one hq0 hq1
  have hq0c : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hP0 := qPochhammerInfIn_ofReal_self_ne_zero hq0 hq1
  have s1 := qPochhammerInfIn_succ_shift ((q : ℂ) ^ (α + 1)) hq
  rw [show (q : ℂ) ^ (α + 1) * q = (q : ℂ) ^ (α + 1 + 1) by
    rw [Complex.cpow_add (α + 1) 1 hq0c, Complex.cpow_one]] at s1
  have s2 := qPochhammerInfIn_succ_shift ((q : ℂ) ^ (α - β + 1)) hq
  rw [show (q : ℂ) ^ (α - β + 1) * q = (q : ℂ) ^ (α - β + 1 + 1) by
    rw [Complex.cpow_add (α - β + 1) 1 hq0c, Complex.cpow_one]] at s2
  have s3 := qPochhammerInfIn_succ_shift ((q : ℂ) ^ β) hq
  rw [show (q : ℂ) ^ β * q = (q : ℂ) ^ (β + 1) by
    rw [Complex.cpow_add β 1 hq0c, Complex.cpow_one]] at s3
  have huv : (q : ℂ) ^ β * (q : ℂ) ^ (α - β + 1) = (q : ℂ) ^ (α + 1) := by
    rw [← Complex.cpow_add _ _ hq0c]
    congr 1
    ring
  rw [s1] at hα
  have hw : 1 - (q : ℂ) ^ (α + 1) ≠ 0 := left_ne_zero_of_mul hα
  have hP3 : qPochhammerInfIn ((q : ℂ) ^ (α + 1 + 1)) q ≠ 0 := right_ne_zero_of_mul hα
  unfold gaussianBinomialCC
  rw [show (β - 1 + 1 : ℂ) = β by ring, show (α - (β - 1) + 1 : ℂ) = α - β + 1 + 1 by ring,
    show (α + 1 - β + 1 : ℂ) = α - β + 1 + 1 by ring, s1, s2, s3, ← huv]
  rw [← huv] at hw
  field_simp
  all_goals ring

/-- **Second Pascal law** `[α+1,β]_q = [α,β]_q + q^{α+1-β} [α,β-1]_q`, whenever
`(q^{α+1};q)_∞ ≠ 0`. -/
theorem gaussianBinomialCC_succ_left' (hq0 : 0 < q) (hq1 : q < 1) {α β : ℂ}
    (hα : qPochhammerInfIn ((q : ℂ) ^ (α + 1)) q ≠ 0) :
    gaussianBinomialCC q (α + 1) β =
      gaussianBinomialCC q α β + (q : ℂ) ^ (α + 1 - β) * gaussianBinomialCC q α (β - 1) := by
  have hq := norm_ofReal_lt_one hq0 hq1
  have hq0c : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hP0 := qPochhammerInfIn_ofReal_self_ne_zero hq0 hq1
  have s1 := qPochhammerInfIn_succ_shift ((q : ℂ) ^ (α + 1)) hq
  rw [show (q : ℂ) ^ (α + 1) * q = (q : ℂ) ^ (α + 1 + 1) by
    rw [Complex.cpow_add (α + 1) 1 hq0c, Complex.cpow_one]] at s1
  have s2 := qPochhammerInfIn_succ_shift ((q : ℂ) ^ (α + 1 - β)) hq
  rw [show (q : ℂ) ^ (α + 1 - β) * q = (q : ℂ) ^ (α + 1 - β + 1) by
    rw [Complex.cpow_add (α + 1 - β) 1 hq0c, Complex.cpow_one]] at s2
  have s3 := qPochhammerInfIn_succ_shift ((q : ℂ) ^ β) hq
  rw [show (q : ℂ) ^ β * q = (q : ℂ) ^ (β + 1) by
    rw [Complex.cpow_add β 1 hq0c, Complex.cpow_one]] at s3
  have htu : (q : ℂ) ^ (α + 1 - β) * (q : ℂ) ^ β = (q : ℂ) ^ (α + 1) := by
    rw [← Complex.cpow_add _ _ hq0c]
    congr 1
    ring
  rw [s1] at hα
  have hw : 1 - (q : ℂ) ^ (α + 1) ≠ 0 := left_ne_zero_of_mul hα
  have hP3 : qPochhammerInfIn ((q : ℂ) ^ (α + 1 + 1)) q ≠ 0 := right_ne_zero_of_mul hα
  unfold gaussianBinomialCC
  rw [show (β - 1 + 1 : ℂ) = β by ring, show (α - (β - 1) + 1 : ℂ) = α + 1 - β + 1 by ring,
    show (α - β + 1 : ℂ) = α + 1 - β by ring, s1, s2, s3, ← htu]
  rw [← htu] at hw
  field_simp
  all_goals ring

/-- **Agreement at a natural lower argument**: `[α,k]_q = (q^{α-k+1};q)_k/(q;q)_k`, whenever
`(q^{α+1};q)_∞ ≠ 0`. -/
theorem gaussianBinomialCC_natCast (hq0 : 0 < q) (hq1 : q < 1) (α : ℂ) (k : ℕ)
    (hα : qPochhammerInfIn ((q : ℂ) ^ (α + 1)) q ≠ 0) :
    gaussianBinomialCC q α k = gaussianBinomialC (q : ℂ) α k := by
  have hq := norm_ofReal_lt_one hq0 hq1
  have hq0c : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hP0 := qPochhammerInfIn_ofReal_self_ne_zero hq0 hq1
  have hPk : finiteQPochhammerIn (q : ℂ) q k ≠ 0 := finiteQPochhammerIn_self_ne_zero hq k
  have t1 := qPochhammerInfIn_eq_finite_mul_shift (q : ℂ) hq k
  rw [show (q : ℂ) * (q : ℂ) ^ k = (q : ℂ) ^ ((k : ℂ) + 1) by
    rw [Complex.cpow_add _ _ hq0c, Complex.cpow_natCast, Complex.cpow_one, mul_comm]] at t1
  have t2 := qPochhammerInfIn_eq_finite_mul_shift ((q : ℂ) ^ (α - k + 1)) hq k
  rw [show (q : ℂ) ^ (α - k + 1) * (q : ℂ) ^ k = (q : ℂ) ^ (α + 1) by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0c]
    congr 1
    ring] at t2
  have hPk1 : qPochhammerInfIn ((q : ℂ) ^ ((k : ℂ) + 1)) q ≠ 0 := by
    rw [t1] at hP0
    exact right_ne_zero_of_mul hP0
  unfold gaussianBinomialCC gaussianBinomialC
  rw [t2, t1]
  field_simp

end Fabius
