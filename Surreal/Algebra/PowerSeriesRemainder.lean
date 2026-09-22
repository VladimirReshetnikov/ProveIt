import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# An exact second-order formal remainder

Removing the first two coefficients of a formal power series gives a fixed
shifted series. The resulting identity is algebraic and requires no analytic
convergence assumption.
-/

namespace Surreal.FormalPowerSeries

noncomputable section

variable {R : Type*} [Semiring R]

/-- The formal series left after removing the constant and linear terms. -/
def secondOrderRemainder (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n => f.coeff (n + 2))

@[simp] theorem coeff_secondOrderRemainder (f : PowerSeries R) (n : ℕ) :
    (secondOrderRemainder f).coeff n = f.coeff (n + 2) :=
  PowerSeries.coeff_mk _ _

@[simp] theorem constantCoeff_secondOrderRemainder (f : PowerSeries R) :
    (secondOrderRemainder f).constantCoeff = f.coeff 2 := rfl

/-- Exact second-order expansion in the formal power-series ring. -/
theorem eq_linear_add_sq_mul_secondOrderRemainder (f : PowerSeries R) :
    f = PowerSeries.C (f.coeff 0) + PowerSeries.C (f.coeff 1) * PowerSeries.X +
      PowerSeries.X ^ 2 * secondOrderRemainder f := by
  have h := PowerSeries.eq_X_pow_mul_shift_add_trunc 2 f
  rw [show (2 : ℕ) = 1 + 1 from rfl, PowerSeries.trunc_succ,
    PowerSeries.trunc_one_left] at h
  simpa only [Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_monomial,
    PowerSeries.monomial_eq_C_mul_X_pow, pow_one, add_comm, secondOrderRemainder] using h

end

end Surreal.FormalPowerSeries
