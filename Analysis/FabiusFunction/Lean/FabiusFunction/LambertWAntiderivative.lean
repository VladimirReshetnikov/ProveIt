import FabiusFunction.PrincipalLambertW
import FabiusFunction.LowerLambertW

/-!
# Antiderivatives of the real Lambert branches

The Lambert W guide's "two basic antiderivatives": on any interval inside a
differentiable branch,

`∫ W(x) dx = e^{W(x)} (W(x)² - W(x) + 1) + C = x (W(x) - 1 + 1/W(x)) + C`

and, away from `x = 0`,

`∫ W(x)/x dx = W(x) + ½ W(x)² + C`.

## One identity does all the work

Both real branches satisfy `W' = (e^W (1 + W))⁻¹`, i.e. `W' · e^W · (1 + W) = 1`.
That single fact is all the antiderivative formulas use:

* `d/dx [e^W (W² - W + 1)] = W' e^W (W² - W + 1) + e^W (2W - 1) W'
  = W' e^W (W² + W) = W · (W' e^W (1 + W)) = W`;
* `d/dx [W + ½ W²] = W' (1 + W) = (e^W)⁻¹ = W / (W e^W) = W / x` once
  `W e^W = x` and `x ≠ 0`.

So the formulas are proved first for an arbitrary function `W` carrying that
derivative identity at a point (`Fabius.LambertAntiderivative`), and both
branches are instances.  Stated this way the lemmas apply to any local
inverse of `w ↦ w eʷ`, and the two branches share one proof instead of two.
-/

set_option autoImplicit false

open Set

namespace Fabius

namespace LambertAntiderivative

variable {W : ℝ → ℝ} {x : ℝ}

/-- **The antiderivative of a Lambert branch.**  If `W' = (e^W (W + 1))⁻¹` at
`x` and `W x ≠ -1`, then `e^W (W² - W + 1)` has derivative `W` at `x`. -/
theorem hasDerivAt_exp_mul_sq_sub_add_one
    (hW : HasDerivAt W (Real.exp (W x) * (W x + 1))⁻¹ x) (hne : W x ≠ -1) :
    HasDerivAt (fun y => Real.exp (W y) * (W y ^ 2 - W y + 1)) (W x) x := by
  have h1 : W x + 1 ≠ 0 := fun h => hne (by linarith)
  have he : Real.exp (W x) ≠ 0 := (Real.exp_pos _).ne'
  have hexp : HasDerivAt (fun y => Real.exp (W y))
      (Real.exp (W x) * (Real.exp (W x) * (W x + 1))⁻¹) x := hW.exp
  -- `HasDerivAt.pow`/`.sub`/`.add_const` return the function in Pi form, which
  -- is definitionally `fun y => W y ^ 2 - W y + 1`; only the derivative needs
  -- rewriting, and `congr_deriv` does that.
  have hpoly : HasDerivAt (fun y => W y ^ 2 - W y + 1)
      (2 * W x * (Real.exp (W x) * (W x + 1))⁻¹ - (Real.exp (W x) * (W x + 1))⁻¹) x :=
    (((hW.pow 2).sub hW).add_const 1).congr_deriv (by norm_num)
  refine (hexp.mul hpoly).congr_deriv ?_
  field_simp
  ring

/-- The same antiderivative in the guide's `x`-form: with `W e^W = x` and
`W x ≠ 0`, `e^W (W² - W + 1) = x (W - 1 + 1/W)`. -/
theorem exp_mul_sq_sub_add_one_eq (hx : W x * Real.exp (W x) = x) (h0 : W x ≠ 0) :
    Real.exp (W x) * (W x ^ 2 - W x + 1) = x * (W x - 1 + 1 / W x) := by
  have hsub : x * (W x - 1 + 1 / W x) =
      (W x * Real.exp (W x)) * (W x - 1 + 1 / W x) := by rw [hx]
  rw [hsub]
  field_simp

/-- **The antiderivative of `W/x`.**  If `W' = (e^W (W + 1))⁻¹` at `x` with
`W x ≠ -1`, `W e^W = x`, and `x ≠ 0`, then `W + ½ W²` has derivative
`W x / x` at `x`.  (The branch point `W = -1` sits at `x = -1/e ≠ 0`, so it
must be excluded separately from `x ≠ 0`.) -/
theorem hasDerivAt_add_half_sq
    (hW : HasDerivAt W (Real.exp (W x) * (W x + 1))⁻¹ x) (hne : W x ≠ -1)
    (hx : W x * Real.exp (W x) = x) (hx0 : x ≠ 0) :
    HasDerivAt (fun y => W y + W y ^ 2 / 2) (W x / x) x := by
  have h1 : W x + 1 ≠ 0 := fun h => hne (by linarith)
  have he : Real.exp (W x) ≠ 0 := (Real.exp_pos _).ne'
  have hW0 : W x ≠ 0 := by
    intro h
    apply hx0
    rw [← hx, h, zero_mul]
  -- `W / x = (e^W)⁻¹`, from the defining equation
  have hkey : W x / x = (Real.exp (W x))⁻¹ := by
    rw [div_eq_iff hx0]
    calc W x = (Real.exp (W x))⁻¹ * (W x * Real.exp (W x)) := by field_simp
      _ = (Real.exp (W x))⁻¹ * x := by rw [hx]
  have h2 : HasDerivAt (fun y => W y ^ 2 / 2)
      (2 * W x * (Real.exp (W x) * (W x + 1))⁻¹ / 2) x := by
    have := hW.pow 2
    simpa [pow_two, mul_comm, mul_assoc, mul_left_comm] using this.div_const 2
  refine (hW.add h2).congr_deriv ?_
  rw [hkey]
  field_simp
  ring

end LambertAntiderivative

/-! ### The two branches -/

/-- On `(-1/e, ∞)`, `e^{W₀}(W₀² - W₀ + 1)` is an antiderivative of `W₀`. -/
theorem hasDerivAt_principalLambertW_antiderivative {x : ℝ} (hx : -Real.exp (-1) < x) :
    HasDerivAt (fun y => Real.exp (principalLambertW y) *
      (principalLambertW y ^ 2 - principalLambertW y + 1)) (principalLambertW x) x :=
  LambertAntiderivative.hasDerivAt_exp_mul_sq_sub_add_one (principalLambertW_hasDerivAt hx)
    (neg_one_lt_principalLambertW hx).ne'

/-- On `(-1/e, 0)`, `e^{W₋₁}(W₋₁² - W₋₁ + 1)` is an antiderivative of `W₋₁`. -/
theorem hasDerivAt_lowerLambertW_antiderivative {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    HasDerivAt (fun y => Real.exp (lowerLambertW y) *
      (lowerLambertW y ^ 2 - lowerLambertW y + 1)) (lowerLambertW x) x :=
  LambertAntiderivative.hasDerivAt_exp_mul_sq_sub_add_one (lowerLambertW_hasDerivAt hx)
    (lowerLambertW_lt_neg_one hx).ne

/-- On `(-1/e, ∞) \ {0}`, `W₀ + ½ W₀²` is an antiderivative of `W₀(x)/x`. -/
theorem hasDerivAt_principalLambertW_add_half_sq {x : ℝ} (hx : -Real.exp (-1) < x)
    (hx0 : x ≠ 0) :
    HasDerivAt (fun y => principalLambertW y + principalLambertW y ^ 2 / 2)
      (principalLambertW x / x) x :=
  LambertAntiderivative.hasDerivAt_add_half_sq (principalLambertW_hasDerivAt hx)
    (neg_one_lt_principalLambertW hx).ne' (principalLambertW_mul_exp hx.le) hx0

/-- On `(-1/e, 0)`, `W₋₁ + ½ W₋₁²` is an antiderivative of `W₋₁(x)/x`. -/
theorem hasDerivAt_lowerLambertW_add_half_sq {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    HasDerivAt (fun y => lowerLambertW y + lowerLambertW y ^ 2 / 2)
      (lowerLambertW x / x) x :=
  LambertAntiderivative.hasDerivAt_add_half_sq (lowerLambertW_hasDerivAt hx)
    (lowerLambertW_lt_neg_one hx).ne (lowerLambertW_mul_exp hx) hx.2.ne

end Fabius
