import Mathlib.Tactic

/-!
# Rational parametrization of a split quadratic norm

The field algebra in the full-surreal contrast following `odg:ex:pell2`.
The factors x+ry and x-ry are s and c/s, respectively.
-/

namespace Surreal.SplitNorm

variable {K : Type*} [Field K] [CharZero K]

/-- First coordinate of the split-norm parametrization. -/
def x (s c : K) : K := (s + c / s) / 2

/-- Second coordinate of the split-norm parametrization. -/
def y (r s c : K) : K := (s - c / s) / (2 * r)

/-- Every nonzero parameter gives a point of the prescribed quadratic norm. -/
theorem equation (r s c : K) (hr : r ≠ 0) (hs : s ≠ 0) :
    x s c ^ 2 - r ^ 2 * y r s c ^ 2 = c := by
  unfold x y
  field_simp
  ring

/-- Dropping both inverse terms gives a zero-norm pair. -/
theorem truncated_equation (r s : K) (hr : r ≠ 0) :
    (s / 2) ^ 2 - r ^ 2 * (s / (2 * r)) ^ 2 = 0 := by
  field_simp
  ring

end Surreal.SplitNorm
