import Mathlib

/-!
# Higher Newton--Kummer cocycle

This file isolates the finite commutative-ring algebra of the higher Newton--Kummer
construction in the post-report closure audit.  Its sign, asymptotic, trace, and Kummer-degree
analysis remain paper-level statements.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace RankOneNewtonKummer

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The Newton numerator at the geometric nodes `1, p, ..., p^(m-1)`. -/
def newtonProduct (m : ℕ) (u p : R) : R :=
  ∏ j ∈ Finset.range m, (u - p ^ j)

/-- The denominator obtained by evaluating the Newton numerator at the next node. -/
def endpointProduct (m : ℕ) (p : R) : R :=
  newtonProduct m (p ^ m) p

/-- The cross-base Newton--Kummer cocycle. -/
def newtonCocycle (m : ℕ) (p q u v : R) : R :=
  newtonProduct m u p * endpointProduct m q -
    newtonProduct m v q * endpointProduct m p

/-- Order one is the third-order Kummer determinant used earlier in the report. -/
theorem newtonCocycle_one (p q u v : R) :
    newtonCocycle 1 p q u v = (u - 1) * (q - 1) - (v - 1) * (p - 1) := by
  simp [newtonCocycle, endpointProduct, newtonProduct]

theorem newtonProduct_natPower_eq_zero {m n : ℕ} (h : n < m) (p : R) :
    newtonProduct m (p ^ n) p = 0 := by
  rw [newtonProduct]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr h)
  simp

/-- Every common integral exponent below the interpolation order kills the cocycle. -/
theorem newtonCocycle_natPower_eq_zero_of_lt {m n : ℕ} (h : n < m) (p q : R) :
    newtonCocycle m p q (p ^ n) (q ^ n) = 0 := by
  rw [newtonCocycle, newtonProduct_natPower_eq_zero h,
    newtonProduct_natPower_eq_zero h]
  ring

/-- The endpoint exponent also kills the cocycle. -/
theorem newtonCocycle_endpoint_eq_zero (m : ℕ) (p q : R) :
    newtonCocycle m p q (p ^ m) (q ^ m) = 0 := by
  rw [newtonCocycle, endpointProduct, endpointProduct]
  ring

/-- Every common natural exponent at or below `m` kills the adaptive cocycle. -/
theorem newtonCocycle_natPower_eq_zero {m n : ℕ} (h : n ≤ m) (p q : R) :
    newtonCocycle m p q (p ^ n) (q ^ n) = 0 := by
  rcases h.eq_or_lt with rfl | hlt
  · exact newtonCocycle_endpoint_eq_zero n p q
  · exact newtonCocycle_natPower_eq_zero_of_lt hlt p q

/-- Order three calibrates the genuine exponent two. -/
theorem calibration_two (p q : R) :
    newtonCocycle 3 p q (p ^ 2) (q ^ 2) = 0 := by
  exact newtonCocycle_natPower_eq_zero (by omega) p q

/-- Order three also calibrates the genuine exponent three. -/
theorem calibration_three (p q : R) :
    newtonCocycle 3 p q (p ^ 3) (q ^ 3) = 0 := by
  exact newtonCocycle_natPower_eq_zero (by omega) p q

end RankOneNewtonKummer
end LeanProofs.TwoBaseIntegerExponent
