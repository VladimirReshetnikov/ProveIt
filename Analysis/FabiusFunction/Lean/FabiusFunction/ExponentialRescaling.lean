import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Rescaling formal series and exponentials

The derivative of `f(c X)` is `c f'(c X)`, already over a commutative
semiring. The coefficient proof avoids substitution hypotheses and division.
Applied to the exponential over a commutative rational algebra, it supplies
the shared derivative used by the Nörlund and Abel polynomial calculations.

The zero-parameter and parameter-addition specializations retain the public
names previously defined only over `ℚ` in `NorlundDiagonal`.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

/-- The formal chain rule for scalar rescaling, without division or subtraction. -/
theorem derivative_rescale {R : Type*} [CommSemiring R] (c : R) (f : R⟦X⟧) :
    d⁄dX R (rescale c f) = C c * rescale c (d⁄dX R f) := by
  ext n
  simp only [coeff_derivative, coeff_rescale, coeff_C_mul, pow_succ]
  ac_rfl

section Exponential

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The derivative of `exp(c X)` is `c exp(c X)` over any commutative rational algebra. -/
theorem derivative_rescale_exp (c : R) :
    d⁄dX R (rescale c (exp R)) = C c * rescale c (exp R) := by
  rw [derivative_rescale, PowerSeries.derivative_exp]

/-- The exponential with zero parameter is the unit series. -/
theorem rescale_zero_exp : rescale (0 : R) (exp R) = 1 := by
  rw [rescale_zero, RingHom.comp_apply, constantCoeff_exp, map_one]

/-- Adding one to the exponential parameter multiplies by `exp(X)`. -/
theorem rescale_exp_add_one (c : R) :
    rescale (c + 1) (exp R) = rescale c (exp R) * exp R := by
  rw [← exp_mul_exp_eq_exp_add, rescale_one, RingHom.id_apply]

end Exponential

end Fabius
