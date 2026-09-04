import FabiusFunction.LambertBranchDichotomy
import FabiusFunction.LambertWElementaryBounds
import FabiusFunction.LowerLambertW

/-!
# The addition identity for Lambert values

The Lambert W guide's "addition identity": if `a = W(x)` and `b = W(y)` on
any branches, with `a, b ≠ 0`, then

`(a + b) e^{a+b} = x·y·(1/a + 1/b)`,

so `a + b` is again a Lambert value, of `x·y·(1/a + 1/b)`, on whichever branch
contains it.

## Nothing here is branch-specific

The identity uses only `e^a = x/a` and `e^b = y/b`, so it is stated for
arbitrary reals `a, b` satisfying their defining equations
(`mul_exp_add_of_mul_exp`), with no Lambert function in sight.  The two
branch consequences then read the result through the uniqueness theorems of
`PrincipalLambertW` and `LowerLambertW`: `a + b ≥ -1` puts the sum on the
principal branch, `a + b ≤ -1` (with the product in the lower branch's
domain) on the lower one.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- **The addition identity**, for any two reals satisfying their defining
equations: if `a e^a = x` and `b e^b = y` with `a, b ≠ 0`, then
`(a + b) e^{a+b} = x y (1/a + 1/b)`. -/
theorem mul_exp_add_of_mul_exp {a b x y : ℝ} (ha : a * Real.exp a = x)
    (hb : b * Real.exp b = y) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (a + b) * Real.exp (a + b) = x * y * (1 / a + 1 / b) := by
  rw [Real.exp_add, ← ha, ← hb]
  field_simp
  ring

/-- **Principal-branch consequence.**  If `a e^a = x`, `b e^b = y`, `a, b ≠ 0`
and `-1 ≤ a + b`, then `a + b = W₀(x y (1/a + 1/b))`. -/
theorem add_eq_principalLambertW_of_mul_exp {a b x y : ℝ} (ha : a * Real.exp a = x)
    (hb : b * Real.exp b = y) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : -1 ≤ a + b) :
    a + b = principalLambertW (x * y * (1 / a + 1 / b)) := by
  have h := mul_exp_add_of_mul_exp ha hb ha0 hb0
  refine principalLambertW_unique ?_ hab h
  -- the product lies in the principal domain because it is a value of `w e^w`,
  -- and `-e⁻¹ ≤ w e^w` for every real `w` (the minimum is at `w = -1`)
  rw [← h]
  exact neg_exp_neg_one_le_mul_exp (a + b)

/-- **Lower-branch consequence.**  If `a e^a = x`, `b e^b = y`, `a, b ≠ 0`,
`a + b ≤ -1`, and the product lies in `[-1/e, 0)`, then
`a + b = W₋₁(x y (1/a + 1/b))`. -/
theorem add_eq_lowerLambertW_of_mul_exp {a b x y : ℝ} (ha : a * Real.exp a = x)
    (hb : b * Real.exp b = y) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a + b ≤ -1)
    (hmem : x * y * (1 / a + 1 / b) ∈ Ico (-Real.exp (-1)) 0) :
    a + b = lowerLambertW (x * y * (1 / a + 1 / b)) :=
  lowerLambertW_unique_of_mem_Ico hmem hab (mul_exp_add_of_mul_exp ha hb ha0 hb0)

/-- The guide's form: for `a = W₀(x)` and `b = W₀(y)` with `x, y > 0`, the sum
of the principal values is the principal value at `x y (1/a + 1/b)`. -/
theorem principalLambertW_add_principalLambertW {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    principalLambertW x + principalLambertW y =
      principalLambertW (x * y * (1 / principalLambertW x + 1 / principalLambertW y)) := by
  have hx' : -Real.exp (-1) ≤ x := by linarith [Real.exp_pos (-1)]
  have hy' : -Real.exp (-1) ≤ y := by linarith [Real.exp_pos (-1)]
  have ha0 : principalLambertW x ≠ 0 := by
    intro h
    have := principalLambertW_mul_exp hx'
    rw [h, zero_mul] at this
    exact hx.ne' this.symm
  have hb0 : principalLambertW y ≠ 0 := by
    intro h
    have := principalLambertW_mul_exp hy'
    rw [h, zero_mul] at this
    exact hy.ne' this.symm
  exact add_eq_principalLambertW_of_mul_exp (principalLambertW_mul_exp hx')
    (principalLambertW_mul_exp hy') ha0 hb0
    (by linarith [principalLambertW_pos hx, principalLambertW_pos hy])

end Fabius
