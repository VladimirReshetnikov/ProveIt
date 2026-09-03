import FabiusFunction.PrincipalLambertW

/-!
# Elementary global bounds for the principal Lambert branch

For every `x ≥ 0`,

`x / (1 + x) ≤ W₀(x) ≤ log (1 + x) ≤ x`,

with all three inequalities strict when `x > 0`.  This is the "global
elementary principal-branch bounds" theorem of the Lambert W guide.

## The one inequality behind all three

Write `x = w·eʷ` with `w = W₀(x) ≥ 0`.  Then

* `W₀(x) ≤ log (1 + x)` says `eʷ ≤ 1 + w·eʷ`, and
* `x / (1 + x) ≤ W₀(x)` says `w·eʷ ≤ w·(1 + w·eʷ)`, which for `w > 0` is the
  same inequality `eʷ ≤ 1 + w·eʷ` again;

and that inequality is `1 - w ≤ e⁻ʷ`, the tangent-line bound for the
exponential.  So the module proves the bounds first for an arbitrary
nonnegative real `w`, as statements about `w` and `w·eʷ` with no inverse
function in sight, and then reads them off for `W₀` through
`principalLambertW_mul_exp`.  The third inequality, `log (1 + x) ≤ x`, is
Mathlib's `Real.log_le_sub_one_of_pos`.

Stating the bounds for an arbitrary `w ≥ 0` is the natural generality: the
guide's theorem is the case `w = W₀(x)`, but the inequalities hold for every
nonnegative real and are used that way whenever a Lambert value is only known
through its defining equation.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-! ### The inequality behind the bounds -/

/-- **The tangent-line bound in Lambert form.**  For every real `w`,
`eʷ ≤ 1 + w·eʷ`; this is `1 - w ≤ e⁻ʷ` multiplied through by `eʷ`, and needs
no sign condition on `w`. -/
theorem exp_le_one_add_mul_exp_self (w : ℝ) :
    Real.exp w ≤ 1 + w * Real.exp w := by
  have h := Real.add_one_le_exp (-w)
  have hpos := Real.exp_pos w
  have key : Real.exp w * (1 - w) ≤ 1 := by
    calc Real.exp w * (1 - w) ≤ Real.exp w * Real.exp (-w) := by
          apply mul_le_mul_of_nonneg_left _ hpos.le
          linarith
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith

/-- The strict form, for every `w ≠ 0`. -/
theorem exp_lt_one_add_mul_exp_self {w : ℝ} (hw : w ≠ 0) :
    Real.exp w < 1 + w * Real.exp w := by
  have h := Real.add_one_lt_exp (neg_ne_zero.mpr hw)
  have hpos := Real.exp_pos w
  have key : Real.exp w * (1 - w) < 1 := by
    calc Real.exp w * (1 - w) < Real.exp w * Real.exp (-w) := by
          apply mul_lt_mul_of_pos_left _ hpos
          linarith
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith

/-! ### The bounds for an arbitrary nonnegative real -/

/-- For `w ≥ 0`, `w ≤ log (1 + w·eʷ)`: the upper bound on the Lambert value
in terms of its own image. -/
theorem le_log_one_add_mul_exp (w : ℝ) :
    w ≤ Real.log (1 + w * Real.exp w) :=
  calc w = Real.log (Real.exp w) := (Real.log_exp w).symm
    _ ≤ Real.log (1 + w * Real.exp w) :=
      Real.log_le_log (Real.exp_pos w) (exp_le_one_add_mul_exp_self w)

/-- The strict form, for every `w ≠ 0`. -/
theorem lt_log_one_add_mul_exp {w : ℝ} (hw : w ≠ 0) :
    w < Real.log (1 + w * Real.exp w) :=
  calc w = Real.log (Real.exp w) := (Real.log_exp w).symm
    _ < Real.log (1 + w * Real.exp w) :=
      Real.log_lt_log (Real.exp_pos w) (exp_lt_one_add_mul_exp_self hw)

/-- For `w ≥ 0`, `w·eʷ / (1 + w·eʷ) ≤ w`: the rational lower bound on the
Lambert value in terms of its own image. -/
theorem mul_exp_div_one_add_le {w : ℝ} (hw : 0 ≤ w) :
    w * Real.exp w / (1 + w * Real.exp w) ≤ w := by
  have hpos : 0 < 1 + w * Real.exp w := by positivity
  rw [div_le_iff₀ hpos]
  have := exp_le_one_add_mul_exp_self w
  nlinarith [Real.exp_pos w]

/-- The strict form for `w > 0`. -/
theorem mul_exp_div_one_add_lt {w : ℝ} (hw : 0 < w) :
    w * Real.exp w / (1 + w * Real.exp w) < w := by
  have hpos : 0 < 1 + w * Real.exp w := by positivity
  rw [div_lt_iff₀ hpos]
  have := exp_lt_one_add_mul_exp_self hw.ne'
  nlinarith [Real.exp_pos w]

/-! ### The principal branch on the nonnegative axis -/

/-- The principal branch is nonnegative on the nonnegative axis: monotonicity
from `W₀(0) = 0`. -/
theorem principalLambertW_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ principalLambertW x := by
  have h0 : (0 : ℝ) ∈ Ici (-Real.exp (-1)) := by
    simp only [mem_Ici]; linarith [Real.exp_pos (-1)]
  have hx' : x ∈ Ici (-Real.exp (-1)) := by
    simp only [mem_Ici]; linarith [Real.exp_pos (-1)]
  have := principalLambertW_strictMonoOn.monotoneOn h0 hx' hx
  simpa [principalLambertW_zero] using this

/-- The principal branch is positive on the positive axis. -/
theorem principalLambertW_pos {x : ℝ} (hx : 0 < x) : 0 < principalLambertW x := by
  have h0 : (0 : ℝ) ∈ Ici (-Real.exp (-1)) := by
    simp only [mem_Ici]; linarith [Real.exp_pos (-1)]
  have hx' : x ∈ Ici (-Real.exp (-1)) := by
    simp only [mem_Ici]; linarith [Real.exp_pos (-1)]
  have := principalLambertW_strictMonoOn h0 hx' hx
  simpa [principalLambertW_zero] using this

/-- **Global elementary principal-branch bounds, upper half.**  For `x ≥ 0`,
`W₀(x) ≤ log (1 + x)`. -/
theorem principalLambertW_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    principalLambertW x ≤ Real.log (1 + x) := by
  have hz : -Real.exp (-1) ≤ x := by linarith [Real.exp_pos (-1)]
  have h := le_log_one_add_mul_exp (principalLambertW x)
  rwa [principalLambertW_mul_exp hz] at h

/-- Strict for `x > 0`. -/
theorem principalLambertW_lt_log_one_add {x : ℝ} (hx : 0 < x) :
    principalLambertW x < Real.log (1 + x) := by
  have hz : -Real.exp (-1) ≤ x := by linarith [Real.exp_pos (-1)]
  have h := lt_log_one_add_mul_exp (principalLambertW_pos hx).ne'
  rwa [principalLambertW_mul_exp hz] at h

/-- **Global elementary principal-branch bounds, lower half.**  For `x ≥ 0`,
`x / (1 + x) ≤ W₀(x)`. -/
theorem div_one_add_le_principalLambertW {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ principalLambertW x := by
  have hz : -Real.exp (-1) ≤ x := by linarith [Real.exp_pos (-1)]
  have h := mul_exp_div_one_add_le (principalLambertW_nonneg hx)
  rwa [principalLambertW_mul_exp hz] at h

/-- Strict for `x > 0`. -/
theorem div_one_add_lt_principalLambertW {x : ℝ} (hx : 0 < x) :
    x / (1 + x) < principalLambertW x := by
  have hz : -Real.exp (-1) ≤ x := by linarith [Real.exp_pos (-1)]
  have h := mul_exp_div_one_add_lt (principalLambertW_pos hx)
  rwa [principalLambertW_mul_exp hz] at h

/-- The principal branch is at most its argument on the nonnegative axis:
`W₀(x) ≤ x`, the outer inequality of the chain. -/
theorem principalLambertW_le_self {x : ℝ} (hx : 0 ≤ x) : principalLambertW x ≤ x :=
  (principalLambertW_le_log_one_add hx).trans
    (by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)])

/-- **The full chain.**  For `x ≥ 0`,
`x / (1 + x) ≤ W₀(x) ∧ W₀(x) ≤ log (1 + x) ∧ log (1 + x) ≤ x`. -/
theorem principalLambertW_elementary_bounds {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ principalLambertW x ∧
      principalLambertW x ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ x :=
  ⟨div_one_add_le_principalLambertW hx, principalLambertW_le_log_one_add hx,
    by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)]⟩

end Fabius
