import FabiusFunction.QPochhammerLogDerivative
import FabiusFunction.QBinomialTheoremInfinite
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Divisor sums from the logarithmic derivative of `(q;q)_∞`

For `‖q‖ < 1`,

`-q (q;q)_∞' / (q;q)_∞ = ∑_{j ≥ 1} j q^j/(1 - q^j) = ∑_{n ≥ 1} σ₁(n) q^n`.

The derivative of `q ↦ (q;q)_∞ = exp ∑_j log(1 - q^{j+1})` is obtained by termwise
differentiation of the logarithmic series on discs `‖q‖ < r < 1` (with the dominating series
`∑ (j+1) r^j/(1-r)`), and the Lambert series `∑_{j≥1} j q^j/(1-q^j)` is rearranged into the
divisor-sum series by Mathlib's `tsum_pow_div_one_sub_eq_tsum_sigma`.

## Main declarations

* `hasDerivAt_tsum_log_one_sub_pow_succ`, `hasDerivAt_qPochhammerInfIn_self`.
* `tsum_lambert_sigma_one`: the Lambert series of `σ₁`.
* `neg_mul_deriv_div_qPochhammerInfIn_self`: the divisor-sum identity.
-/

set_option autoImplicit false

open Filter Topology ArithmeticFunction
open scoped sigma

namespace Fabius

/-- **The Lambert series of `σ₁`**: `∑_{j ≥ 0} (j+1) q^{j+1}/(1 - q^{j+1}) = ∑_{n ≥ 1} σ₁(n) q^n`. -/
theorem tsum_lambert_sigma_one {q : ℂ} (hq : ‖q‖ < 1) :
    ∑' j : ℕ, ((j : ℂ) + 1) * q ^ (j + 1) / (1 - q ^ (j + 1)) =
      ∑' n : ℕ+, (σ 1 n : ℂ) * q ^ (n : ℕ) := by
  have h := tsum_pow_div_one_sub_eq_tsum_sigma hq 1
  simp only [pow_one] at h
  rw [← h, tsum_pnat_eq_tsum_succ (f := fun m : ℕ => (m : ℂ) * q ^ m / (1 - q ^ m))]
  exact tsum_congr fun j => by simp

/-- The logarithms `log(1 - q^{j+1})` are summable for `‖q‖ < 1`. -/
theorem summable_log_one_sub_pow_succ {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun j : ℕ => Complex.log (1 - q ^ (j + 1)) :=
  (summable_log_one_sub_mul_pow hq q).congr fun j => by rw [pow_succ']

/-- **Termwise differentiation of `∑_j log(1 - y^{j+1})`** on the disc `‖y‖ < r < 1`. -/
theorem hasDerivAt_tsum_log_one_sub_pow_succ {r : ℝ} (hr1 : r < 1) {q : ℂ} (hqr : ‖q‖ < r) :
    HasDerivAt (fun y : ℂ => ∑' j : ℕ, Complex.log (1 - y ^ (j + 1)))
      (∑' j : ℕ, -(((j : ℂ) + 1) * q ^ j) / (1 - q ^ (j + 1))) q := by
  have hr0 : 0 < 1 - r := by linarith
  have hrpos : 0 ≤ r := (norm_nonneg q).trans hqr.le
  have hq1 : ‖q‖ < 1 := hqr.trans hr1
  have hu : Summable fun j : ℕ => ((j : ℝ) + 1) * r ^ j / (1 - r) := by
    refine Summable.div_const ?_ _
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by rwa [Real.norm_of_nonneg hrpos])
    have h2 := summable_geometric_of_lt_one hrpos hr1
    refine (h1.add h2).congr fun j => ?_
    simp [add_mul]
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun j y => Complex.log (1 - y ^ (j + 1)))
    (g' := fun j y => -(((j : ℂ) + 1) * y ^ j) / (1 - y ^ (j + 1)))
    (u := fun j : ℕ => ((j : ℝ) + 1) * r ^ j / (1 - r)) (t := Metric.ball (0 : ℂ) r)
    hu Metric.isOpen_ball Metric.isPreconnected_ball (fun j y hy => ?_) (fun j y hy => ?_)
    (by simpa using hqr) (summable_log_one_sub_pow_succ hq1) (by simpa using hqr)
  · have hy1 : ‖y‖ < 1 := (by simpa using hy : ‖y‖ < r).trans hr1
    have h1 : HasDerivAt (fun y : ℂ => 1 - y ^ (j + 1)) (-(((j : ℂ) + 1) * y ^ j)) y := by
      have := (hasDerivAt_pow (j + 1) y).const_sub 1
      simpa [Nat.add_sub_cancel] using this
    refine h1.clog ?_
    have : ‖-(y ^ (j + 1))‖ < 1 := by
      rw [norm_neg, norm_pow]
      exact pow_lt_one₀ (norm_nonneg y) hy1 (Nat.succ_ne_zero j)
    simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one this
  · have hy : ‖y‖ < r := by simpa using hy
    rw [norm_div, norm_neg, norm_mul, norm_pow]
    have hden : 1 - r ≤ ‖1 - y ^ (j + 1)‖ := by
      have := one_sub_le_norm_one_sub_mul_pow (q := y) (hy.trans hr1).le hy j
      rwa [← pow_succ'] at this
    have hnum : ‖(j : ℂ) + 1‖ * ‖y‖ ^ j ≤ ((j : ℝ) + 1) * r ^ j := by
      have hc : ‖(j : ℂ) + 1‖ = (j : ℝ) + 1 := by
        rw [← Nat.cast_succ, Complex.norm_natCast, Nat.cast_succ]
      rw [hc]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) hy.le j) (by positivity)
    exact div_le_div₀ (by positivity) hnum hr0 hden

/-- `(q;q)_∞ = exp ∑_j log(1 - q^{j+1})` for `‖q‖ < 1`. -/
theorem qPochhammerInfIn_self_eq_cexp {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInfIn q q = Complex.exp (∑' j : ℕ, Complex.log (1 - q ^ (j + 1))) := by
  rw [qPochhammerInfIn_eq_cexp_tsum_log hq hq]
  simp_rw [← pow_succ']

/-- **The derivative of `q ↦ (q;q)_∞`**: `-(q;q)_∞ ∑_j (j+1) q^j/(1 - q^{j+1})` for `‖q‖ < 1`. -/
theorem hasDerivAt_qPochhammerInfIn_self {q : ℂ} (hq : ‖q‖ < 1) :
    HasDerivAt (fun y : ℂ => qPochhammerInfIn y y)
      (-(qPochhammerInfIn q q * ∑' j : ℕ, ((j : ℂ) + 1) * q ^ j / (1 - q ^ (j + 1)))) q := by
  obtain ⟨r, hqr, hr1⟩ := exists_between hq
  have hL := (hasDerivAt_tsum_log_one_sub_pow_succ hr1 hqr).cexp
  refine (hL.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hq : q ∈ Metric.ball (0 : ℂ) 1)]
      with y hy
    exact qPochhammerInfIn_self_eq_cexp (by simpa using hy)
  · rw [← qPochhammerInfIn_self_eq_cexp hq]
    simp_rw [neg_div]
    rw [tsum_neg, mul_neg]

/-- **Divisor sums**: `-q · (q;q)_∞' / (q;q)_∞ = ∑_{n ≥ 1} σ₁(n) q^n` for `‖q‖ < 1`, where
`(q;q)_∞'` is the derivative of `hasDerivAt_qPochhammerInfIn_self`. -/
theorem neg_mul_deriv_div_qPochhammerInfIn_self {q : ℂ} (hq : ‖q‖ < 1) :
    -q * (-(qPochhammerInfIn q q * ∑' j : ℕ, ((j : ℂ) + 1) * q ^ j / (1 - q ^ (j + 1)))) /
        qPochhammerInfIn q q = ∑' n : ℕ+, (σ 1 n : ℂ) * q ^ (n : ℕ) := by
  have hP : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hq
  rw [← tsum_lambert_sigma_one hq]
  have key : -q * (-(qPochhammerInfIn q q *
      ∑' j : ℕ, ((j : ℂ) + 1) * q ^ j / (1 - q ^ (j + 1)))) / qPochhammerInfIn q q =
      q * ∑' j : ℕ, ((j : ℂ) + 1) * q ^ j / (1 - q ^ (j + 1)) := by
    field_simp
    all_goals ring
  rw [key, ← tsum_mul_left]
  exact tsum_congr fun j => by ring

end Fabius
