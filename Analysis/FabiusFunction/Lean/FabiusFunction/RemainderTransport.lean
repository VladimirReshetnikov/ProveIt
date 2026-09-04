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
* `Fabius.transport_first_order`: part (2), `p0:eq:transport-first-order` — the
  displacement is `-ε(x₀)/f₀'(x₀)` up to an explicit error.

Part (2) turns out not to need a second-order Taylor estimate.  The mean value
point does all the work: `x - x₀ = -ε(x₀)/f'(ξ)` is *exact*, so the entire error
is the mismatch between `f'(ξ)` and `f₀'(x₀)` — a perturbation `ε'(ξ)` and a
curvature term `M₂|ξ - x₀|`.  The same `ξ` also supplies the bound of
`transport_bound`, so part (1) is not an input to part (2).  Accordingly the
`|f₀''| ≤ M₂` of the volume enters only as a Lipschitz bound on `f₀'`, which is
weaker and is exactly what the argument consumes.
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

/-- `p0:eq:transport-first-order`: the displacement is `-ε(x₀)/f₀'(x₀)` up to an
explicit error.

The Lipschitz hypothesis on `f₀'` is what the volume writes as `|f₀''| ≤ M₂`;
stating it as a Lipschitz bound rather than a second derivative is both weaker
and exactly what the proof consumes, and `lipschitzOn_of_abs_deriv_le` supplies
it from the second-derivative form.

Note that the mean value point does all the work: `x - x₀ = -ε(x₀)/f'(ξ)` is
exact, and the whole error term is the difference between `f'(ξ)` and `f₀'(x₀)`
— a perturbation `ε'` and a curvature `M₂|ξ - x₀|`.  The bound of
`transport_bound` is not needed as an input; the same `ξ` supplies it. -/
theorem transport_first_order {D : Set ℝ} (hD : Convex ℝ D)
    {f₀ ε f₀' ε' : ℝ → ℝ} {m θ M₂ : ℝ}
    (hf₀ : ∀ z ∈ D, HasDerivAt f₀ (f₀' z) z)
    (hε : ∀ z ∈ D, HasDerivAt ε (ε' z) z)
    (hm : ∀ z ∈ D, m ≤ f₀' z)
    (hθb : ∀ z ∈ D, |ε' z| ≤ θ)
    (hlip : ∀ u ∈ D, ∀ v ∈ D, |f₀' u - f₀' v| ≤ M₂ * |u - v|)
    (hM₂ : 0 ≤ M₂) (hm0 : 0 < m) (hθm : θ < m)
    {x x₀ lam : ℝ} (hx : x ∈ D) (hx₀ : x₀ ∈ D)
    (h₀ : f₀ x₀ = lam) (hxe : f₀ x + ε x = lam) :
    |(x - x₀) + ε x₀ / f₀' x₀|
      ≤ |ε x₀| / (m * (m - θ)) * (M₂ * |ε x₀| / (m - θ) + θ) := by
  have hmθ : (0:ℝ) < m - θ := by linarith
  have hf₀x₀ : 0 < f₀' x₀ := lt_of_lt_of_le hm0 (hm x₀ hx₀)
  have hθ0 : (0:ℝ) ≤ θ := le_trans (abs_nonneg _) (hθb x₀ hx₀)
  rcases eq_or_ne x x₀ with hxx | hne
  · subst hxx
    have hε0 : ε x = 0 := by
      rw [h₀] at hxe
      linarith
    rw [hε0]
    simp
  · have hminD : min x x₀ ∈ D := by
      rcases min_cases x x₀ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> assumption
    have hmaxD : max x x₀ ∈ D := by
      rcases max_cases x x₀ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> assumption
    have hsub : Set.Icc (min x x₀) (max x x₀) ⊆ D :=
      (convex_iff_ordConnected.mp hD).out hminD hmaxD
    have hab : min x x₀ < max x x₀ := min_lt_max.mpr hne
    have hF : ∀ z ∈ D, HasDerivAt (fun w => f₀ w + ε w) (f₀' z + ε' z) z :=
      fun z hz => (hf₀ z hz).add (hε z hz)
    have hcont : ContinuousOn (fun w => f₀ w + ε w) (Set.Icc (min x x₀) (max x x₀)) :=
      fun z hz => ((hF z (hsub hz)).continuousAt).continuousWithinAt
    obtain ⟨ξ, hξmem, hξ⟩ := exists_hasDerivAt_eq_slope
      (fun w => f₀ w + ε w) (fun w => f₀' w + ε' w) hab hcont
      (fun z hz => hF z (hsub (Set.Ioo_subset_Icc_self hz)))
    have hξD : ξ ∈ D := hsub (Set.Ioo_subset_Icc_self hξmem)
    have hxne : x - x₀ ≠ 0 := sub_ne_zero.mpr hne
    have hslope : f₀' ξ + ε' ξ = -ε x₀ / (x - x₀) := by
      rw [hξ]
      have hFx : f₀ x + ε x = lam := hxe
      have hFx₀ : f₀ x₀ + ε x₀ = lam + ε x₀ := by rw [h₀]
      rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left h.le, max_eq_right h.le, hFx, hFx₀]
        have hne' : x₀ - x ≠ 0 := sub_ne_zero.mpr h.ne'
        field_simp
        ring
      · rw [min_eq_right h.le, max_eq_left h.le, hFx, hFx₀]
        field_simp
        ring
    have hFξ : m - θ ≤ f₀' ξ + ε' ξ := by
      have h1 := hm ξ hξD
      have h2 := abs_le.mp (hθb ξ hξD)
      linarith [h2.1]
    have hFξpos : 0 < f₀' ξ + ε' ξ := lt_of_lt_of_le hmθ hFξ
    have hGne : f₀' ξ + ε' ξ ≠ 0 := hFξpos.ne'
    have hf0ne : f₀' x₀ ≠ 0 := hf₀x₀.ne'
    -- the mean value point gives the displacement exactly
    have hmul : (x - x₀) * (f₀' ξ + ε' ξ) = -ε x₀ := by
      rw [hslope]
      field_simp
    have hdisp : x - x₀ = -ε x₀ / (f₀' ξ + ε' ξ) := by
      rw [eq_div_iff hGne]
      exact hmul
    have habsdisp : |x - x₀| ≤ |ε x₀| / (m - θ) := by
      rw [hdisp, abs_div, abs_neg, abs_of_pos hFξpos]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hmθ hFξ
    have hkey : (x - x₀) + ε x₀ / f₀' x₀
        = ε x₀ * ((f₀' ξ + ε' ξ) - f₀' x₀) / (f₀' x₀ * (f₀' ξ + ε' ξ)) := by
      rw [hdisp]
      field_simp
      ring
    have hms : max x x₀ - min x x₀ = |x - x₀| := by
      rw [max_sub_min_eq_abs, abs_sub_comm]
    have hξx₀ : |ξ - x₀| ≤ |x - x₀| := by
      rw [abs_sub_le_iff]
      constructor <;>
        linarith [hξmem.1, hξmem.2, min_le_right x x₀, le_max_right x x₀, hms]
    have hnum : |(f₀' ξ + ε' ξ) - f₀' x₀| ≤ M₂ * |ε x₀| / (m - θ) + θ := by
      have hsplit : (f₀' ξ + ε' ξ) - f₀' x₀ = (f₀' ξ - f₀' x₀) + ε' ξ := by ring
      have hcurv : |f₀' ξ - f₀' x₀| ≤ M₂ * |ε x₀| / (m - θ) := by
        refine le_trans (hlip ξ hξD x₀ hx₀) ?_
        calc M₂ * |ξ - x₀| ≤ M₂ * |x - x₀| := by nlinarith
          _ ≤ M₂ * (|ε x₀| / (m - θ)) := by nlinarith
          _ = M₂ * |ε x₀| / (m - θ) := by ring
      calc |(f₀' ξ + ε' ξ) - f₀' x₀| = |(f₀' ξ - f₀' x₀) + ε' ξ| := by rw [hsplit]
        _ ≤ |f₀' ξ - f₀' x₀| + |ε' ξ| := abs_add_le _ _
        _ ≤ M₂ * |ε x₀| / (m - θ) + θ := by linarith [hθb ξ hξD]
    have hP : (0:ℝ) < f₀' x₀ * (f₀' ξ + ε' ξ) := mul_pos hf₀x₀ hFξpos
    have hden : m * (m - θ) ≤ f₀' x₀ * (f₀' ξ + ε' ξ) := by
      have := hm x₀ hx₀
      nlinarith
    have hBnn : (0:ℝ) ≤ M₂ * |ε x₀| / (m - θ) + θ := by positivity
    rw [hkey, abs_div, abs_mul, abs_of_pos hP]
    have hstep1 : |ε x₀| * |(f₀' ξ + ε' ξ) - f₀' x₀| / (f₀' x₀ * (f₀' ξ + ε' ξ))
        ≤ |ε x₀| * (M₂ * |ε x₀| / (m - θ) + θ) / (f₀' x₀ * (f₀' ξ + ε' ξ)) := by
      have hle : |ε x₀| * |(f₀' ξ + ε' ξ) - f₀' x₀|
          ≤ |ε x₀| * (M₂ * |ε x₀| / (m - θ) + θ) :=
        mul_le_mul_of_nonneg_left hnum (abs_nonneg _)
      have := mul_le_mul_of_nonneg_right hle (le_of_lt (inv_pos.mpr hP))
      simpa [div_eq_mul_inv] using this
    have hstep2 : |ε x₀| * (M₂ * |ε x₀| / (m - θ) + θ) / (f₀' x₀ * (f₀' ξ + ε' ξ))
        ≤ |ε x₀| * (M₂ * |ε x₀| / (m - θ) + θ) / (m * (m - θ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    calc |ε x₀| * |(f₀' ξ + ε' ξ) - f₀' x₀| / (f₀' x₀ * (f₀' ξ + ε' ξ))
        ≤ |ε x₀| * (M₂ * |ε x₀| / (m - θ) + θ) / (m * (m - θ)) := le_trans hstep1 hstep2
      _ = |ε x₀| / (m * (m - θ)) * (M₂ * |ε x₀| / (m - θ) + θ) := by ring

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
