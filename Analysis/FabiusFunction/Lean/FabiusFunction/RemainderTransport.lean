import FabiusFunction.MeanValueBracket
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Transport of a controlled forward remainder

The transseries volume's `p0:thm:remainder-transport` is the estimate that turns
a bound on a *forward* perturbation into a bound on the displacement of the
*root*.  With `f = f₀ + ε`, `f₀' ≥ m > 0` and `sup |ε'| ≤ θ < m`, if `x₀` solves
`f₀(x₀) = λ` and `x` solves `f(x) = λ`, then

`|x - x₀| ≤ |ε(x₀)| / (m - θ)`.

This is `p0:eq:transport-bound`, and it is what every application chapter uses to
convert a truncation error in the forward expansion into an error in the
inverse.

Two things the formal statement clarifies.

The hypothesis on `ε` is *Lipschitz*, not a derivative bracket, and it cannot be
a derivative bracket of the kind `MeanValueBracket` supplies: `ε` is a
perturbation with `|ε'| ≤ θ`, so its derivative bracket is `-θ ≤ ε' ≤ θ`, whose
lower end is negative, and `Fabius.abs_sub_le_of_le_deriv` needs `0 ≤ m`
(necessarily — see its docstring).  What is available is the two-sided
`‖ε'‖ ≤ θ` Lipschitz bound, which is a different Mathlib lemma.  The core
theorem below therefore takes the Lipschitz property as its hypothesis, and
`Fabius.lipschitzOn_of_abs_deriv_le` supplies it from a derivative bound.

The lower bracket on `f₀`, by contrast, is exactly
`Fabius.mul_abs_sub_le_abs_sub_of_le_deriv`, and needs no sign hypothesis.

## Main results

* `Fabius.lipschitzOn_of_abs_deriv_le`: `|ε'| ≤ θ` gives `|ε u - ε v| ≤ θ|u - v|`.
* `Fabius.transport_bound_mul`: the division-free form,
  `(m - θ)|x - x₀| ≤ |ε(x₀)|`.
* `Fabius.transport_bound`: `p0:eq:transport-bound` itself.

Not formalized here: part (2), the first-order law with explicit error
`p0:eq:transport-first-order`, which needs `f₀ ∈ C²` and a second-order Taylor
estimate.
-/

set_option autoImplicit false

namespace Fabius

open Set

/-- A two-sided derivative bound gives a Lipschitz bound.  This is the form the
perturbation `ε` needs: unlike the upper mean-value bracket, it requires no sign
condition, because it does not go through monotonicity. -/
theorem lipschitzOn_of_abs_deriv_le {D : Set ℝ} (hD : Convex ℝ D) {ε ε' : ℝ → ℝ}
    {θ : ℝ} (hε : ∀ z ∈ D, HasDerivWithinAt ε (ε' z) D z)
    (hb : ∀ z ∈ D, |ε' z| ≤ θ) {u v : ℝ} (hu : u ∈ D) (hv : v ∈ D) :
    |ε u - ε v| ≤ θ * |u - v| := by
  have hb' : ∀ z ∈ D, ‖ε' z‖ ≤ θ := by
    intro z hz
    rw [Real.norm_eq_abs]
    exact hb z hz
  have h := hD.norm_image_sub_le_of_norm_hasDerivWithin_le hε hb' hv hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- `p0:eq:transport-bound`, division-free.  The forward perturbation `ε` at the
unperturbed root controls the displacement of the root, with the deficit `m - θ`
between the slope floor and the perturbation's Lipschitz constant as the only
denominator. -/
theorem transport_bound_mul {D : Set ℝ} (hD : Convex ℝ D) {f₀ ε : ℝ → ℝ} {m θ : ℝ}
    (hf₀c : ContinuousOn f₀ D) (hf₀d : DifferentiableOn ℝ f₀ (interior D))
    (hm : ∀ z ∈ interior D, m ≤ deriv f₀ z)
    (hlip : ∀ u ∈ D, ∀ v ∈ D, |ε u - ε v| ≤ θ * |u - v|)
    {x x₀ lam : ℝ} (hx : x ∈ D) (hx₀ : x₀ ∈ D)
    (hx₀eq : f₀ x₀ = lam) (hxeq : f₀ x + ε x = lam) :
    (m - θ) * |x - x₀| ≤ |ε x₀| := by
  have hlow : m * |x - x₀| ≤ |f₀ x - f₀ x₀| :=
    mul_abs_sub_le_abs_sub_of_le_deriv hD hf₀c hf₀d hm hx hx₀
  have heq : f₀ x - f₀ x₀ = -ε x := by
    rw [hx₀eq]
    linarith
  rw [heq, abs_neg] at hlow
  have hsplit : ε x₀ + (ε x - ε x₀) = ε x := by ring
  have h2 : |ε x| ≤ |ε x₀| + θ * |x - x₀| := by
    calc |ε x| = |ε x₀ + (ε x - ε x₀)| := by rw [hsplit]
      _ ≤ |ε x₀| + |ε x - ε x₀| := abs_add_le _ _
      _ ≤ |ε x₀| + θ * |x - x₀| := by linarith [hlip x hx x₀ hx₀]
  linarith

/-- `p0:eq:transport-bound`: `|x - x₀| ≤ |ε(x₀)| / (m - θ)`. -/
theorem transport_bound {D : Set ℝ} (hD : Convex ℝ D) {f₀ ε : ℝ → ℝ} {m θ : ℝ}
    (hf₀c : ContinuousOn f₀ D) (hf₀d : DifferentiableOn ℝ f₀ (interior D))
    (hm : ∀ z ∈ interior D, m ≤ deriv f₀ z)
    (hlip : ∀ u ∈ D, ∀ v ∈ D, |ε u - ε v| ≤ θ * |u - v|)
    (hθ : θ < m) {x x₀ lam : ℝ} (hx : x ∈ D) (hx₀ : x₀ ∈ D)
    (hx₀eq : f₀ x₀ = lam) (hxeq : f₀ x + ε x = lam) :
    |x - x₀| ≤ |ε x₀| / (m - θ) := by
  have hmθ : (0:ℝ) < m - θ := by linarith
  rw [le_div_iff₀ hmθ]
  have h := transport_bound_mul hD hf₀c hf₀d hm hlip hx hx₀ hx₀eq hxeq
  linarith

end Fabius
