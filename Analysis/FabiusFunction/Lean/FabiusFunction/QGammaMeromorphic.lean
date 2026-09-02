import FabiusFunction.ComplexGaussianBinomial
import FabiusFunction.QGammaLogDerivative
import FabiusFunction.QPochhammerOrderDerivative
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The complex `q`-gamma function and the generalized `q`-Pochhammer symbol as meromorphic functions

For `0 < q < 1`, `Γ_q(z) = (q;q)_∞ (1-q)^{1-z}/(q^z;q)_∞` is a quotient of entire functions of
`z`, hence meromorphic on `ℂ` (`meromorphicOn_qGammaC`), holomorphic away from the zeros of the
denominator (`differentiableOn_qGammaC`), and the recurrence
`Γ_q(z+1) = (1-q^z)/(1-q) · Γ_q(z)` holds at every `z` off the poles (`qGammaC_add_one`).

It is genuinely a *continuation* of the real `q`-gamma function: `qGammaC_ofReal` proves
`Γ_q(x) = qGamma q x` for real `x`, identifying the `Complex.cpow` definition with the
`Real.rpow` one.  Together these are the meromorphic-continuation clause of thm:qgamma-basic.

Likewise the generalized symbol `(a;q)_α = (a;q)_∞/(aq^α;q)_∞` is meromorphic on `ℂ`
(`meromorphicOn_qPochhammerC`) and holomorphic on every open set avoiding the poles
(`differentiableOn_qPochhammerC`); it is moreover nonvanishing there provided `(a;q)_∞ ≠ 0`
(`qPochhammerC_ne_zero`) — without that hypothesis it can vanish identically, as at `a = 1`.
This is the holomorphy clause of prop:order-derivative.
-/

set_option autoImplicit false

open Filter Topology Set

namespace Fabius

/-- `z ↦ (q^z;q)_∞` is entire for `0 < ‖q‖ < 1`. -/
theorem differentiable_qPochhammerInfIn_cpow {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (a : ℂ) :
    Differentiable ℂ fun z : ℂ => qPochhammerInfIn (a * q ^ z) q := by
  have h1 : Differentiable ℂ fun z : ℂ => a * q ^ z := fun z =>
    ((hasDerivAt_const_cpow' hq0 z).const_mul a).differentiableAt
  exact (differentiable_qPochhammerInfIn hq).comp h1

section QGamma

variable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
include hq0 hq1

omit hq0 in
/-- The numerator `z ↦ (q;q)_∞ (1-q)^{1-z}` is entire. -/
theorem differentiable_qGammaC_num :
    Differentiable ℂ fun z : ℂ => qPochhammerInfIn (q : ℂ) q * (1 - (q : ℂ)) ^ (1 - z) := by
  have h0 : (1 - (q : ℂ)) ≠ 0 := by
    intro h
    have : (q : ℂ) = 1 := by linear_combination -h
    have : q = 1 := by exact_mod_cast this
    linarith
  refine Differentiable.const_mul ?_ _
  exact fun z => ((hasDerivAt_const_cpow' h0 (1 - z)).comp z
    ((hasDerivAt_id z).const_sub 1)).differentiableAt

/-- The denominator `z ↦ (q^z;q)_∞` is entire. -/
theorem differentiable_qGammaC_den :
    Differentiable ℂ fun z : ℂ => qPochhammerInfIn ((q : ℂ) ^ z) q := by
  have := differentiable_qPochhammerInfIn_cpow (norm_ofReal_lt_one hq0 hq1)
    (by exact_mod_cast hq0.ne') 1
  simpa using this

/-- **`Γ_q` is meromorphic on `ℂ`** (thm:qgamma-basic, meromorphic continuation). -/
theorem meromorphicOn_qGammaC : MeromorphicOn (qGammaC q) univ := by
  intro z _
  have hN := (differentiable_qGammaC_num hq1).analyticAt z
  have hD := (differentiable_qGammaC_den hq0 hq1).analyticAt z
  exact hN.meromorphicAt.div hD.meromorphicAt

/-- `Γ_q` is holomorphic away from the zeros of `(q^z;q)_∞`. -/
theorem differentiableOn_qGammaC :
    DifferentiableOn ℂ (qGammaC q) {z : ℂ | qPochhammerInfIn ((q : ℂ) ^ z) q ≠ 0} :=
  (differentiable_qGammaC_num hq1).differentiableOn.div
    (differentiable_qGammaC_den hq0 hq1).differentiableOn fun _ hz => hz

/-- **The recurrence for a complex argument**: `Γ_q(z+1) = (1-q^z)/(1-q) · Γ_q(z)` off the
poles. -/
theorem qGammaC_add_one {z : ℂ} (hz : qPochhammerInfIn ((q : ℂ) ^ z) q ≠ 0) :
    qGammaC q (z + 1) = (1 - (q : ℂ) ^ z) / (1 - (q : ℂ)) * qGammaC q z := by
  have hqc : ‖(q : ℂ)‖ < 1 := norm_ofReal_lt_one hq0 hq1
  have hq0c : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have h1q : (1 - (q : ℂ)) ≠ 0 := by
    intro h
    have : (q : ℂ) = 1 := by linear_combination -h
    have : q = 1 := by exact_mod_cast this
    linarith
  have hshift : qPochhammerInfIn ((q : ℂ) ^ z) q =
      (1 - (q : ℂ) ^ z) * qPochhammerInfIn ((q : ℂ) ^ (z + 1)) q := by
    rw [qPochhammerInfIn_eq_finite_mul_shift _ hqc 1, finiteQPochhammerIn, Finset.prod_range_one,
      pow_zero, mul_one, pow_one, Complex.cpow_add _ _ hq0c, Complex.cpow_one]
  have hz1 : qPochhammerInfIn ((q : ℂ) ^ (z + 1)) q ≠ 0 := by
    intro h
    apply hz
    rw [hshift, h, mul_zero]
  have hpow : (1 - (q : ℂ)) ^ (1 - (z + 1)) = (1 - (q : ℂ)) ^ (1 - z) / (1 - (q : ℂ)) := by
    rw [show (1 : ℂ) - (z + 1) = (1 - z) - 1 by ring, Complex.cpow_sub _ _ h1q, Complex.cpow_one]
  have h1z : (1 : ℂ) - (q : ℂ) ^ z ≠ 0 := by
    intro h
    apply hz
    rw [hshift, h, zero_mul]
  unfold qGammaC
  rw [hpow, hshift]
  field_simp

/-- **The complex `q`-gamma function restricts to the real one.**  For `0 < q < 1` and real
`x`, the `Complex.cpow` definition `qGammaC` agrees with the `Real.rpow` definition `qGamma`.
This is what makes `qGammaC` a *continuation* of `qGamma`: without it, `qGammaC` would merely be
some meromorphic function satisfying a similar recurrence. -/
theorem qGammaC_ofReal (x : ℝ) : qGammaC q (x : ℂ) = ((qGamma q x : ℝ) : ℂ) := by
  have hqn : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq0.le]
    exact hq1
  have hnum : ((qPochhammerInfIn q q : ℝ) : ℂ) = qPochhammerInfIn (q : ℂ) (q : ℂ) :=
    ofReal_qPochhammerInfIn hqn
  have hden : ((qPochhammerInfIn (q ^ x) q : ℝ) : ℂ) =
      qPochhammerInfIn ((q : ℂ) ^ (x : ℂ)) (q : ℂ) := by
    rw [ofReal_qPochhammerInfIn hqn, Complex.ofReal_cpow hq0.le]
  have hpow : (((1 - q) ^ (1 - x) : ℝ) : ℂ) = (1 - (q : ℂ)) ^ (1 - (x : ℂ)) := by
    rw [Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ 1 - q)]
    congr 1 <;> push_cast <;> ring
  unfold qGammaC qGamma
  rw [Complex.ofReal_mul, Complex.ofReal_div, hnum, hden, hpow]
  ring

end QGamma

section OrderHolomorphy

variable {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
include hq hq0

/-- **`(a;q)_α` is meromorphic in `α` on `ℂ`**. -/
theorem meromorphicOn_qPochhammerC (a : ℂ) : MeromorphicOn (fun α => qPochhammerC a q α) univ := by
  intro z _
  have hN : AnalyticAt ℂ (fun _ : ℂ => qPochhammerInfIn a q) z := analyticAt_const
  have hD := (differentiable_qPochhammerInfIn_cpow hq hq0 a).analyticAt z
  exact hN.meromorphicAt.div hD.meromorphicAt

/-- **Holomorphy of `(a;q)_α` on the pole-free set** (prop:order-derivative). -/
theorem differentiableOn_qPochhammerC (a : ℂ) :
    DifferentiableOn ℂ (fun α => qPochhammerC a q α) {α : ℂ | qPochhammerInfIn (a * q ^ α) q ≠ 0} :=
  (differentiableOn_const _).div (differentiable_qPochhammerInfIn_cpow hq hq0 a).differentiableOn
    fun _ hα => hα

omit hq hq0 in
/-- `(a;q)_α ≠ 0` when `(a;q)_∞ ≠ 0` and `α` is not a pole. -/
theorem qPochhammerC_ne_zero {a α : ℂ} (ha : qPochhammerInfIn a q ≠ 0)
    (hα : qPochhammerInfIn (a * q ^ α) q ≠ 0) : qPochhammerC a q α ≠ 0 :=
  div_ne_zero ha hα

end OrderHolomorphy

end Fabius
