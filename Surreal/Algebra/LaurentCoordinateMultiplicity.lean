import Surreal.Algebra.LaurentAlgebraization
import Surreal.Algebra.PolynomialCoordinateMultiplicity

/-!
# Local multiplicity of a finite Laurent sum

Clearing negative frequencies multiplies the formal germ by a unit.
Thus a unit-valued coordinate with nonzero linear term identifies the germ's
native power-series order with the native multiplicity of the cleared
polynomial. This is the formal algebra in `trigonometry:thm:polyroots`.
-/

namespace Surreal.LaurentCoordinateMultiplicity

open Polynomial Finset

noncomputable section
variable {K : Type*} [Field K]

/-- A finite Laurent sum evaluated in a formal unit coordinate. -/
def localSeries (N : ℕ) (c : ℤ → K) (φ : (PowerSeries K)ˣ) : PowerSeries K :=
  ∑ k ∈ Icc (-(N : ℤ)) N, PowerSeries.C (c k) * (φ ^ k).val

/-- Clearing negative powers is an exact identity of formal power series. -/
theorem cleared_identity (N : ℕ) (c : ℤ → K) (φ : (PowerSeries K)ˣ) :
    φ.val ^ N * localSeries N c φ =
      (LaurentAlgebraization.polynomial N c).eval₂ PowerSeries.C φ.val := by
  classical
  rw [localSeries, LaurentAlgebraization.polynomial, Polynomial.eval₂_finsetSum, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hb := mem_Icc.mp hk
  have he : φ.val ^ (k + N).toNat = (φ ^ k).val * φ.val ^ N := by
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega), zpow_add, Units.val_mul, zpow_natCast,
      Units.val_pow_eq_pow_val]
  rw [eval₂_monomial, he]
  ring

/-- The formal Laurent germ has the cleared polynomial's multiplicity in any simple coordinate. -/
theorem order_localSeries (N : ℕ) (c : ℤ → K)
    (hp : LaurentAlgebraization.polynomial N c ≠ 0)
    (φ : (PowerSeries K)ˣ) (z : K) (hz : φ.val.constantCoeff = z)
    (hlinear : φ.val.coeff 1 ≠ 0) :
    (localSeries N c φ).order =
      ((LaurentAlgebraization.polynomial N c).rootMultiplicity z : ℕ∞) := by
  have hunit : φ.val.constantCoeff ≠ 0 :=
    (φ.isUnit.map PowerSeries.constantCoeff).ne_zero
  have horder := PolynomialCoordinateMultiplicity.order_zero_of_constantCoeff_ne_zero φ.val hunit
  have h := congrArg PowerSeries.order (cleared_identity N c φ)
  rw [PowerSeries.order_mul, PowerSeries.order_pow, horder, smul_zero, zero_add,
    PolynomialCoordinateMultiplicity.order_eval_of_linear_ne_zero _ hp z φ.val hz hlinear] at h
  exact h

end
end Surreal.LaurentCoordinateMultiplicity
