import FabiusFunction.GaussianBinomialBounds
import FabiusFunction.GaussianBinomialFixedColumnRate
import FabiusFunction.JacobiTripleProduct
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Gaussian-binomial asymptotics for a nome greater than one

Gaussian-binomial reciprocity transfers the contracting-nome estimates at
`q⁻¹` to every real `q > 1`.  This gives the manuscript's two asymptotic
regimes with their printed normalization:

* for fixed `k`, the normalized coefficient
  `(q⁻¹;q⁻¹)_k q^(-k(n-k)) [n,k]_q` differs from one by
  `O((q⁻¹)^(n-k+1))`;
* the central coefficient satisfies
  `[2m,m]_q ~ q^(m²) / (q⁻¹;q⁻¹)_∞`.

Both results retain the strict hypothesis `1 < q`, so reciprocity never meets
the singular value `q = 0` and the reciprocal nome has norm strictly below
one.

## Main declarations

* `gaussianBinomial_gt_one_fixedColumn_relativeError_isBigO` is the effective
  fixed-column estimate in the printed multiplicative normalization.
* `gaussianBinomial_gt_one_central_isEquivalent` is the central asymptotic
  equivalence.
-/

set_option autoImplicit false

open Filter Topology Asymptotics
open scoped Asymptotics

namespace Fabius

noncomputable section

/-- **Fixed-column asymptotics for `q > 1`.**  For fixed `k`,

`(q⁻¹;q⁻¹)_k q^(-k(n-k)) [n,k]_q - 1
  = O((q⁻¹)^(n-k+1))`.

Equivalently,
`[n,k]_q = q^(k(n-k)) / (q⁻¹;q⁻¹)_k * (1 + O((q⁻¹)^(n-k+1)))`.
The use of `n - k` is the manuscript's total natural-number normalization;
the proof invokes reciprocity only eventually, once `k ≤ n`. -/
theorem gaussianBinomial_gt_one_fixedColumn_relativeError_isBigO
    {q : ℝ} (hq : 1 < q) (k : ℕ) :
    (fun n : ℕ ↦
      finiteQPochhammerIn q⁻¹ q⁻¹ k *
          ((q ^ (k * (n - k)))⁻¹ * gaussianBinomial q n k) - 1) =O[atTop]
        (fun n : ℕ ↦ (q⁻¹) ^ (n - k + 1)) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hqne : q ≠ 0 := hq0.ne'
  have hqi : ‖q⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq0)]
    exact inv_lt_one_of_one_lt₀ hq
  have hbase := gaussianBinomial_fixedColumn_relativeError_isBigO q⁻¹ hqi k
  refine hbase.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop k] with n hn
  have hreciprocity := gaussianBinomial_inv q hqne hn
  have hpow : q ^ (k * (n - k)) ≠ 0 := pow_ne_zero _ hqne
  have hcancel :
      (q ^ (k * (n - k)))⁻¹ *
          (q ^ (k * (n - k)) * gaussianBinomial q⁻¹ n k) =
        gaussianBinomial q⁻¹ n k := by
    calc
      (q ^ (k * (n - k)))⁻¹ *
          (q ^ (k * (n - k)) * gaussianBinomial q⁻¹ n k) =
          ((q ^ (k * (n - k)))⁻¹ * q ^ (k * (n - k))) *
            gaussianBinomial q⁻¹ n k := by rw [mul_assoc]
      _ = gaussianBinomial q⁻¹ n k := by
        rw [inv_mul_cancel₀ hpow, one_mul]
  rw [hreciprocity, hcancel]

/-- **Central asymptotics for `q > 1`.**  The central Gaussian coefficient
has the exact manuscript normalization

`[2m,m]_q ~ q^(m²) / (q⁻¹;q⁻¹)_∞`.

The nonvanishing of the infinite q-Pochhammer denominator follows from
`|q⁻¹| < 1`; reciprocity then transports the contracting-nome central
limit without any positivity argument for individual coefficients. -/
theorem gaussianBinomial_gt_one_central_isEquivalent {q : ℝ} (hq : 1 < q) :
    (fun m : ℕ ↦ gaussianBinomial q (2 * m) m) ~[atTop]
      (fun m : ℕ ↦ q ^ (m * m) * (qPochhammerInfIn q⁻¹ q⁻¹)⁻¹) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hqne : q ≠ 0 := hq0.ne'
  have hqi : ‖q⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq0)]
    exact inv_lt_one_of_one_lt₀ hq
  have hpochhammer : qPochhammerInfIn q⁻¹ q⁻¹ ≠ 0 :=
    qPochhammerInfIn_self_ne_zero hqi
  have hlimit :
      Tendsto (fun m : ℕ ↦ gaussianBinomial q⁻¹ (2 * m) m) atTop
        (𝓝 (qPochhammerInfIn q⁻¹ q⁻¹)⁻¹) := by
    simpa [gaussianBinomialInt_ofNat] using
      (tendsto_gaussianBinomialInt_central (q := q⁻¹) hqi 0)
  have hconstant :
      (fun m : ℕ ↦ gaussianBinomial q⁻¹ (2 * m) m) ~[atTop]
        (fun _ : ℕ ↦ (qPochhammerInfIn q⁻¹ q⁻¹)⁻¹) :=
    (isEquivalent_const_iff_tendsto (inv_ne_zero hpochhammer)).2 hlimit
  have hpower :
      (fun m : ℕ ↦ q ^ (m * m)) ~[atTop] (fun m : ℕ ↦ q ^ (m * m)) :=
    IsEquivalent.refl
  have hproduct := hpower.mul hconstant
  apply hproduct.congr_left
  filter_upwards with m
  simp only [Pi.mul_apply]
  rw [gaussianBinomial_inv q hqne (show m ≤ 2 * m by omega)]
  have hsub : 2 * m - m = m := by omega
  rw [hsub]

end

end Fabius
