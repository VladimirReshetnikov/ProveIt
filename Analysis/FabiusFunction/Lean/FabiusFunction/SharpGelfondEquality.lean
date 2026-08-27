import FabiusFunction.SharpGelfondBound

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

end Fabius
