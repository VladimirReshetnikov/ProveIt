import FabiusFunction.LambertSeriesLog
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The logarithmic derivative of the infinite q-Pochhammer product

For `‖q‖ < 1` and `‖a‖ < 1`, the product `(a;q)_∞` is differentiable in `a` with

`d/da (a;q)_∞ = -(a;q)_∞ ∑_{j≥0} q^j/(1 - aq^j) = -(a;q)_∞ ∑_{m≥1} a^{m-1}/(1 - q^m)`.

The proof differentiates the logarithm.  On a disc `‖a‖ < r < 1` the series
`∑_j log(1 - aq^j)` may be differentiated termwise, because the derivatives
`-q^j/(1 - aq^j)` are dominated by the summable `‖q‖^j/(1-r)`; exponentiating
gives the first formula.  The Lambert series `∑_m a^m/(m(1-q^m))` may likewise
be differentiated termwise, and since it is minus the logarithm on the disc,
the two derivatives agree, which is the second formula.

## Main declarations

* `summable_pow_div_one_sub_mul_pow`: `∑ q^j/(1 - aq^j)` converges.
* `hasDerivAt_tsum_log_one_sub_mul_pow`: termwise differentiation of the
  logarithmic series.
* `hasDerivAt_qPochhammerInfIn`: the derivative of `a ↦ (a;q)_∞`.
* `hasDerivAt_lambert_series`, `tsum_neg_pow_div_one_sub_mul_pow_eq`,
  `hasDerivAt_qPochhammerInfIn_lambert`: the Lambert-series form.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

variable {q : ℂ}

/-- `1 - r ≤ ‖1 - y q^j‖` when `‖y‖ < r` and `‖q‖ ≤ 1`. -/
theorem one_sub_le_norm_one_sub_mul_pow {r : ℝ} (hq : ‖q‖ ≤ 1) {y : ℂ} (hy : ‖y‖ < r) (j : ℕ) :
    1 - r ≤ ‖1 - y * q ^ j‖ := by
  have h1 : ‖y * q ^ j‖ ≤ r := by
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg y) (pow_le_one₀ (norm_nonneg q) hq)).trans hy.le
  calc 1 - r ≤ 1 - ‖y * q ^ j‖ := by linarith
    _ = ‖(1 : ℂ)‖ - ‖y * q ^ j‖ := by rw [norm_one]
    _ ≤ ‖1 - y * q ^ j‖ := norm_sub_norm_le _ _

/-- The logarithmic-derivative series `∑ q^j/(1 - aq^j)` converges for `‖a‖ < 1`. -/
theorem summable_pow_div_one_sub_mul_pow (hq : ‖q‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) :
    Summable fun j : ℕ => q ^ j / (1 - a * q ^ j) := by
  obtain ⟨r, har, hr1⟩ := exists_between ha
  have hr0 : 0 < 1 - r := by linarith
  refine ((summable_geometric_of_lt_one (norm_nonneg q) hq).div_const (1 - r)).of_norm_bounded
    fun j => ?_
  rw [norm_div, norm_pow]
  exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg q) j) hr0
    (one_sub_le_norm_one_sub_mul_pow hq.le har j)

/-- The logarithms `log(1 - aq^j)` are summable for `‖a‖ < 1`. -/
theorem summable_log_one_sub_mul_pow (hq : ‖q‖ < 1) (a : ℂ) :
    Summable fun j : ℕ => Complex.log (1 - a * q ^ j) := by
  have hs : Summable fun j : ℕ => -(a * q ^ j) :=
    ((summable_geometric_of_norm_lt_one hq).mul_left a).neg
  refine (Complex.summable_log_one_add_of_summable hs).congr fun j => ?_
  rw [← sub_eq_add_neg]

/-- No factor `1 - aq^j` vanishes for `‖a‖ < 1`. -/
theorem one_sub_mul_pow_ne_zero (hq : ‖q‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) (j : ℕ) :
    1 - a * q ^ j ≠ 0 := by
  refine one_sub_ne_zero_of_norm_lt_one ?_
  rw [norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg a) (pow_le_one₀ (norm_nonneg q) hq.le))
    ha

/-- `(a;q)_∞ = exp(∑ log(1 - aq^j))` for `‖a‖ < 1`. -/
theorem qPochhammerInfIn_eq_cexp_tsum_log (hq : ‖q‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) :
    qPochhammerInfIn a q = Complex.exp (∑' j : ℕ, Complex.log (1 - a * q ^ j)) :=
  (Complex.cexp_tsum_eq_tprod (one_sub_mul_pow_ne_zero hq ha)
    (summable_log_one_sub_mul_pow hq a)).symm

/-- **Termwise differentiation of the logarithmic series** on the disc `‖a‖ < r < 1`. -/
theorem hasDerivAt_tsum_log_one_sub_mul_pow (hq : ‖q‖ < 1) {r : ℝ} (hr1 : r < 1) {a : ℂ}
    (har : ‖a‖ < r) :
    HasDerivAt (fun y : ℂ => ∑' j : ℕ, Complex.log (1 - y * q ^ j))
      (∑' j : ℕ, -(q ^ j) / (1 - a * q ^ j)) a := by
  have hr0 : 0 < 1 - r := by linarith
  have ha1 : ‖a‖ < 1 := har.trans hr1
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun j y => Complex.log (1 - y * q ^ j)) (g' := fun j y => -(q ^ j) / (1 - y * q ^ j))
    (u := fun j : ℕ => ‖q‖ ^ j / (1 - r)) (t := Metric.ball (0 : ℂ) r)
    ((summable_geometric_of_lt_one (norm_nonneg q) hq).div_const (1 - r)) Metric.isOpen_ball
    Metric.isPreconnected_ball (fun j y hy => ?_) (fun j y hy => ?_)
    (by simpa using har) (summable_log_one_sub_mul_pow hq a) (by simpa using har)
  · have hy1 : ‖y‖ < 1 := (by simpa using hy : ‖y‖ < r).trans hr1
    have h1 : HasDerivAt (fun y : ℂ => 1 - y * q ^ j) (-(q ^ j)) y := by
      simpa using ((hasDerivAt_id y).mul_const (q ^ j)).const_sub 1
    refine h1.clog ?_
    have : ‖-(y * q ^ j)‖ < 1 := by
      rw [norm_neg, norm_mul, norm_pow]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_right (norm_nonneg y) (pow_le_one₀ (norm_nonneg q) hq.le)) hy1
    simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one this
  · have hy : ‖y‖ < r := by simpa using hy
    rw [norm_div, norm_neg, norm_pow]
    exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg q) j) hr0
      (one_sub_le_norm_one_sub_mul_pow hq.le hy j)

/-- **The derivative of `a ↦ (a;q)_∞`** for `‖a‖ < 1`:
`d/da (a;q)_∞ = -(a;q)_∞ ∑_j q^j/(1 - aq^j)`. -/
theorem hasDerivAt_qPochhammerInfIn (hq : ‖q‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) :
    HasDerivAt (fun y : ℂ => qPochhammerInfIn y q)
      (-(qPochhammerInfIn a q * ∑' j : ℕ, q ^ j / (1 - a * q ^ j))) a := by
  obtain ⟨r, har, hr1⟩ := exists_between ha
  have hL := (hasDerivAt_tsum_log_one_sub_mul_pow hq hr1 har).cexp
  refine (hL.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using ha : a ∈ Metric.ball (0 : ℂ) 1)]
      with y hy
    exact qPochhammerInfIn_eq_cexp_tsum_log hq (by simpa using hy)
  · rw [← qPochhammerInfIn_eq_cexp_tsum_log hq ha]
    simp_rw [neg_div]
    rw [tsum_neg, mul_neg]

/-- **Termwise differentiation of the Lambert series** on the disc `‖a‖ < r < 1`. -/
theorem hasDerivAt_lambert_series (hq : ‖q‖ < 1) {r : ℝ} (hr1 : r < 1) {a : ℂ} (har : ‖a‖ < r) :
    HasDerivAt (fun y : ℂ => ∑' m : ℕ, y ^ (m + 1) / ((m + 1) * (1 - q ^ (m + 1))))
      (∑' m : ℕ, a ^ m / (1 - q ^ (m + 1))) a := by
  have hr0 : 0 ≤ r := (norm_nonneg a).trans har.le
  have ha1 : ‖a‖ < 1 := har.trans hr1
  have h1q : 0 < 1 - ‖q‖ := by linarith
  have hden : ∀ m : ℕ, 1 - ‖q‖ ≤ ‖(1 : ℂ) - q ^ (m + 1)‖ := fun m => by
    have hp : ‖q‖ ^ (m + 1) ≤ ‖q‖ := pow_le_of_le_one (norm_nonneg q) hq.le (Nat.succ_ne_zero m)
    calc 1 - ‖q‖ ≤ 1 - ‖q‖ ^ (m + 1) := by linarith
      _ = ‖(1 : ℂ)‖ - ‖q ^ (m + 1)‖ := by rw [norm_one, norm_pow]
      _ ≤ ‖(1 : ℂ) - q ^ (m + 1)‖ := norm_sub_norm_le _ _
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun m y => y ^ (m + 1) / ((m + 1) * (1 - q ^ (m + 1))))
    (g' := fun m y => y ^ m / (1 - q ^ (m + 1)))
    (u := fun m : ℕ => r ^ m / (1 - ‖q‖)) (t := Metric.ball (0 : ℂ) r)
    ((summable_geometric_of_lt_one hr0 hr1).div_const (1 - ‖q‖)) Metric.isOpen_ball
    Metric.isPreconnected_ball (fun m y _ => ?_) (fun m y hy => ?_)
    (by simpa using har) (summable_lambert_series ha1 hq) (by simpa using har)
  · have h := (hasDerivAt_pow (m + 1) y).div_const (((m : ℂ) + 1) * (1 - q ^ (m + 1)))
    refine h.congr_deriv ?_
    rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      mul_div_mul_left _ _ (Nat.cast_add_one_ne_zero m)]
  · have hy : ‖y‖ < r := by simpa using hy
    rw [norm_div, norm_pow]
    exact div_le_div₀ (pow_nonneg hr0 m) (pow_le_pow_left₀ (norm_nonneg y) hy.le m) h1q (hden m)

/-- The two logarithmic-derivative series agree for `‖a‖ < 1`:
`∑_j -q^j/(1 - aq^j) = -∑_m a^m/(1 - q^{m+1})`. -/
theorem tsum_neg_pow_div_one_sub_mul_pow_eq (hq : ‖q‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) :
    ∑' j : ℕ, -(q ^ j) / (1 - a * q ^ j) = -∑' m : ℕ, a ^ m / (1 - q ^ (m + 1)) := by
  obtain ⟨r, har, hr1⟩ := exists_between ha
  have h1 := hasDerivAt_tsum_log_one_sub_mul_pow hq hr1 har
  have h2 := (hasDerivAt_lambert_series hq hr1 har).neg
  refine h1.unique (h2.congr_of_eventuallyEq ?_)
  filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using ha : a ∈ Metric.ball (0 : ℂ) 1)]
    with y hy
  exact tsum_log_one_sub_geom (by simpa using hy) hq

/-- **The Lambert form of the derivative**: for `‖a‖ < 1`,
`d/da (a;q)_∞ = -(a;q)_∞ ∑_{m≥0} a^m/(1 - q^{m+1})`. -/
theorem hasDerivAt_qPochhammerInfIn_lambert (hq : ‖q‖ < 1) {a : ℂ} (ha : ‖a‖ < 1) :
    HasDerivAt (fun y : ℂ => qPochhammerInfIn y q)
      (-(qPochhammerInfIn a q * ∑' m : ℕ, a ^ m / (1 - q ^ (m + 1)))) a := by
  refine (hasDerivAt_qPochhammerInfIn hq ha).congr_deriv ?_
  have h := tsum_neg_pow_div_one_sub_mul_pow_eq hq ha
  simp_rw [neg_div] at h
  rw [tsum_neg, neg_inj] at h
  rw [h]

end Fabius
