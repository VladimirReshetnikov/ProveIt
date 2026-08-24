import IntegerPoints.IwaniecMozzochi
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Compact smooth-weight bounds for Iwaniec--Mozzochi (8.4)

The partial-summation step in Section 8 fixes the smooth function `sigma`
before quantifying over the scale parameters.  Its eventual implicit constant
may therefore depend on finite bounds for `sigma` and `deriv sigma` on the
compact scaled support window `[0, 8]`.

This module constructs those bounds by the extreme-value theorem.  It assumes
no normalization such as `abs (sigma t) <= 1`, and the resulting constants are
existential witnesses that may depend on the particular fixed function.
-/

open Real Set

namespace LeanProofs.IntegerPoints

/-! ## Generic compactness interfaces -/

/-- A continuous real function has a nonnegative absolute-value bound on every
nonempty compact interval.  The witness is the value at an actual maximizer. -/
theorem exists_abs_bound_on_Icc
    {f : ℝ → ℝ} (hf : Continuous f) {u v : ℝ} (huv : u ≤ v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc u v, |f t| ≤ C := by
  obtain ⟨c, hc, hcmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 huv) hf.norm.continuousOn
  refine ⟨|f c|, abs_nonneg _, ?_⟩
  intro t ht
  simpa [Real.norm_eq_abs] using hcmax ht

/-- If both a real function and its total derivative are continuous, they
have separate nonnegative absolute-value bounds on a compact interval.

The continuity assumptions are stated separately so the exact compactness
boundary is visible; `IsSmoothWeight` supplies both in the Section 8
specialization below. -/
theorem exists_abs_deriv_bounds_on_Icc
    {f : ℝ → ℝ} (hf : Continuous f) (hderiv : Continuous (deriv f))
    {u v : ℝ} (huv : u ≤ v) :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      ∀ t ∈ Set.Icc u v, |f t| ≤ C₀ ∧ |deriv f t| ≤ C₁ := by
  obtain ⟨C₀, hC₀, hbound₀⟩ := exists_abs_bound_on_Icc hf huv
  obtain ⟨C₁, hC₁, hbound₁⟩ := exists_abs_bound_on_Icc hderiv huv
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro t ht
  exact ⟨hbound₀ t ht, hbound₁ t ht⟩

/-! ## The fixed Section 8 weight -/

/-- A fixed Section 8 smooth weight has finite, nonnegative `C⁰` and `C¹`
bounds on the full scaled interval `[0, 8]`.  The constants depend only on
`sigma`, not on `x`, `H`, `M`, the Farey fraction, or the summation index. -/
theorem exists_section8_smoothWeight_abs_deriv_bounds
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) :
    ∃ S₀ S₁ : ℝ, 0 ≤ S₀ ∧ 0 ≤ S₁ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 8,
        |sigma t| ≤ S₀ ∧ |deriv sigma t| ≤ S₁ := by
  apply exists_abs_deriv_bounds_on_Icc
  · exact hsigma.1.continuous
  · exact hsigma.1.continuous_deriv (by simp)
  · norm_num

/-- A one-constant version convenient for downstream product and variation
estimates.  It is derived from the separate maxima without adding a
normalization premise. -/
theorem exists_section8_smoothWeight_C1_bound
    {sigma : ℝ → ℝ} (hsigma : IsSmoothWeight sigma 4 8) :
    ∃ S : ℝ, 0 ≤ S ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 8,
        |sigma t| ≤ S ∧ |deriv sigma t| ≤ S := by
  obtain ⟨S₀, S₁, hS₀, _hS₁, hbounds⟩ :=
    exists_section8_smoothWeight_abs_deriv_bounds hsigma
  refine ⟨max S₀ S₁, hS₀.trans (le_max_left _ _), ?_⟩
  intro t ht
  have htBounds := hbounds t ht
  exact ⟨htBounds.1.trans (le_max_left _ _),
    htBounds.2.trans (le_max_right _ _)⟩

end LeanProofs.IntegerPoints
