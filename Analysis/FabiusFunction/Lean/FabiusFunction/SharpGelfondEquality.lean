import FabiusFunction.SharpGelfondBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Equality in the sharp two-step subaction

The equality analysis of the sharp Gelfond bound (Documents 5/6 of the
second wave, audited): the quartic barrier `u³(1-u) ≤ 27/256` of
`SharpGelfondBound.cube_mul_one_sub_le` is attained **only** at
`u = 3/4` — the value `sin²θ = 3/4` of the extremal period-two orbit
`{1/3, 2/3}`.  This is the uniqueness half of the audit's statement
that the two-step inequality
`|sin θ|²·|sin 2θ| ≤ (√3/2)³` is an equality precisely on the Gelfond
cycle: every strict excursion of the orbit away from `sin² = 3/4`
costs a definite factor, which is what isolates the maximizing cycle
in the `κ∞` layer.

* `cube_mul_one_sub_eq_iff` — `u³(1-u) = 27/256 ↔ u = 3/4`, via the
  exact sum-of-squares identity
  `27/256 - u³(1-u) = ((u-3/4)(u+1/4))² + (u-3/4)²/8`.
* `cube_mul_one_sub_lt` — the strict form: `u ≠ 3/4` implies
  `u³(1-u) < 27/256`.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-- Strict form of the quartic barrier: away from `u = 3/4`,
`u³(1-u) < 27/256`. -/
theorem cube_mul_one_sub_lt {u : ℝ} (hu : u ≠ 3 / 4) :
    u ^ 3 * (1 - u) < 27 / 256 := by
  have hne : u - 3 / 4 ≠ 0 := sub_ne_zero.mpr hu
  have h1 : 0 < (u - 3 / 4) ^ 2 := by positivity
  nlinarith [sq_nonneg ((u - 3 / 4) * (u + 1 / 4)), h1]

/-- **Equality case of the quartic barrier**:
`u³(1-u) = 27/256` if and only if `u = 3/4`. -/
theorem cube_mul_one_sub_eq_iff {u : ℝ} :
    u ^ 3 * (1 - u) = 27 / 256 ↔ u = 3 / 4 := by
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_lt (cube_mul_one_sub_lt hne))
  · rintro rfl
    norm_num

/-- **The equality locus of the extremal orbit value**:
`sin²θ = 3/4` exactly on the Gelfond cycle, `θ ≡ ±π/3 (mod π)`. -/
theorem sin_sq_eq_three_quarters_iff (θ : ℝ) :
    Real.sin θ ^ 2 = 3 / 4 ↔
      ∃ k : ℤ, θ = k * π + π / 3 ∨ θ = k * π - π / 3 := by
  have hpy := Real.sin_sq_add_cos_sq θ
  have hcos23 : Real.cos (2 * π / 3) = -(1 / 2) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
  constructor
  · intro h
    have hc2 : Real.cos (2 * θ) = Real.cos (2 * π / 3) := by
      rw [Real.cos_two_mul, hcos23]
      nlinarith [hpy, h]
    obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp hc2
    · refine ⟨-k, Or.inl ?_⟩
      push_cast
      linarith
    · refine ⟨k, Or.inr ?_⟩
      linarith
  · rintro ⟨k, hk | hk⟩
    · have h2θ : 2 * θ = 2 * π / 3 + (k : ℝ) * (2 * π) := by
        rw [hk]
        ring
      have hcv : Real.cos (2 * θ) = -(1 / 2) := by
        rw [h2θ, Real.cos_add_int_mul_two_pi, hcos23]
      have hct := Real.cos_two_mul θ
      nlinarith [hpy, hcv, hct]
    · have h2θ : 2 * θ = -(2 * π / 3) + (k : ℝ) * (2 * π) := by
        rw [hk]
        ring
      have hcv : Real.cos (2 * θ) = -(1 / 2) := by
        rw [h2θ, show -(2 * π / 3) + (k : ℝ) * (2 * π) =
          -(2 * π / 3) + (k : ℤ) * (2 * π) by norm_num,
          Real.cos_add_int_mul_two_pi, Real.cos_neg, hcos23]
      have hct := Real.cos_two_mul θ
      nlinarith [hpy, hcv, hct]

/-- **Equality in the sharp two-step inequality holds exactly on the
Gelfond cycle**: `|sin θ|²·|sin 2θ| = (√3/2)³ ↔ sin²θ = 3/4` — combined
with `sin_sq_eq_three_quarters_iff`, equality holds precisely for
`θ ≡ ±π/3 (mod π)`, the audit's cycle `{1/3, 2/3}` in the angular
variable. -/
theorem abs_sin_sq_mul_abs_sin_two_mul_eq_iff (θ : ℝ) :
    |Real.sin θ| ^ 2 * |Real.sin (2 * θ)| = (Real.sqrt 3 / 2) ^ 3 ↔
      Real.sin θ ^ 2 = 3 / 4 := by
  have habs : (|Real.sin θ| ^ 2 * |Real.sin (2 * θ)|) ^ 2 =
      4 * ((Real.sin θ ^ 2) ^ 3 * (1 - Real.sin θ ^ 2)) := by
    rw [mul_pow, sq_abs, sq_abs, sin_sq_two_mul]
    ring
  have hrhs : ((Real.sqrt 3 / 2) ^ 3) ^ 2 = 4 * (27 / 256) := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, div_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  constructor
  · intro h
    have hsq := congrArg (fun w : ℝ => w ^ 2) h
    simp only [habs, hrhs] at hsq
    have hquart : (Real.sin θ ^ 2) ^ 3 * (1 - Real.sin θ ^ 2) = 27 / 256 := by
      linarith
    exact cube_mul_one_sub_eq_iff.mp hquart
  · intro h
    have hL0 : 0 ≤ |Real.sin θ| ^ 2 * |Real.sin (2 * θ)| :=
      mul_nonneg (sq_nonneg _) (abs_nonneg _)
    have hR0 : (0:ℝ) ≤ (Real.sqrt 3 / 2) ^ 3 := by positivity
    refine (sq_eq_sq₀ hL0 hR0).mp ?_
    rw [habs, hrhs, h]
    norm_num

end Fabius
