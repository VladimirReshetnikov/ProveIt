import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic

/-!
# A normalized leading factor for formal series

The native factorization by the formal order gives the relative error in
`trigonometry:lem:leading`. After dividing by the first nonzero coefficient,
the remaining unit is one plus a zero-constant formal series. No analytic
convergence or characteristic assumption is needed.
-/

namespace Surreal.FormalPowerSeries

noncomputable section

variable {K : Type*} [Field K]

/-- The relative error after removing the first nonzero monomial. -/
def leadingRemainder (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.C (f.coeff f.order.toNat)⁻¹ * PowerSeries.divXPowOrder f - 1

/-- The normalized relative error has no constant term. -/
theorem constantCoeff_leadingRemainder (f : PowerSeries K) (hf : f ≠ 0) :
    PowerSeries.constantCoeff (leadingRemainder f) = 0 := by
  simp only [leadingRemainder, map_sub, map_mul, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_divXPowOrder, map_one, inv_mul_cancel₀ (PowerSeries.coeff_order hf),
    sub_self]

/-- Exact leading-monomial factorization with a normalized unit. -/
theorem eq_leading_mul_one_add_remainder (f : PowerSeries K) (hf : f ≠ 0) :
    f = PowerSeries.C (f.coeff f.order.toNat) * PowerSeries.X ^ f.order.toNat *
      (1 + leadingRemainder f) := by
  rw [leadingRemainder, add_sub_cancel]
  calc
    f = PowerSeries.X ^ f.order.toNat * PowerSeries.divXPowOrder f :=
      PowerSeries.X_pow_order_mul_divXPowOrder.symm
    _ = (PowerSeries.C (f.coeff f.order.toNat) * PowerSeries.C (f.coeff f.order.toNat)⁻¹) *
        (PowerSeries.X ^ f.order.toNat * PowerSeries.divXPowOrder f) := by
      rw [← map_mul, mul_inv_cancel₀ (PowerSeries.coeff_order hf), map_one, one_mul]
    _ = _ := by ring

end

end Surreal.FormalPowerSeries
