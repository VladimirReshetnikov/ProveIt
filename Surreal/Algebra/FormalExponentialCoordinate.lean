import Surreal.Algebra.PolynomialCoordinateMultiplicity
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Formal exponential units and angular coordinates

Mathlib's exponential multiplication law gives a genuine unit-valued
homomorphism `a ↦ exp(a X)`. Integer powers therefore have the expected
rescaled exponential coefficients. This supplies the local-coordinate
algebra in `trigonometry:thm:polyroots`.
-/

namespace Surreal.FormalExponentialCoordinate

noncomputable section

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The formal exponential of a scalar times the variable. -/
def series (a : K) : PowerSeries K := PowerSeries.rescale a (PowerSeries.exp K)

@[simp] theorem constantCoeff_series (a : K) : (series a).constantCoeff = 1 := by
  simp [series, ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp]

@[simp] theorem coeff_one_series (a : K) : (series a).coeff 1 = a := by
  simp [series, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]

@[simp] theorem series_zero : series (0 : K) = 1 := by simp [series]

/-- Formal exponentials add their scalar parameters under multiplication. -/
theorem series_add (a b : K) : series (a + b) = series a * series b :=
  (PowerSeries.exp_mul_exp_eq_exp_add a b).symm

/-- Every scalar exponential is a unit with opposite-parameter inverse. -/
def exponentialUnit (a : K) : (PowerSeries K)ˣ :=
  Units.mkOfMulEqOne (series a) (series (-a)) (by rw [← series_add, add_neg_cancel, series_zero])

@[simp] theorem exponentialUnit_val (a : K) : (exponentialUnit a).val = series a := rfl

/-- The additive scalar parameter maps homomorphically to multiplicative formal units. -/
def exponentialHom : Multiplicative K →* (PowerSeries K)ˣ where
  toFun a := exponentialUnit a.toAdd
  map_one' := Units.ext series_zero
  map_mul' a b := Units.ext (series_add a.toAdd b.toAdd)

/-- Integer powers of the formal exponential scale its parameter. -/
theorem exponentialUnit_zpow (a : K) (k : ℤ) :
    exponentialUnit a ^ k = exponentialUnit ((k : K) * a) := by
  have h := (map_zpow exponentialHom (Multiplicative.ofAdd a) k).symm
  change exponentialUnit a ^ k = exponentialUnit (k • a) at h
  simpa only [zsmul_eq_mul] using h

/-- The constant coefficient of every integer power is one. -/
theorem constantCoeff_zpow (a : K) (k : ℤ) :
    ((exponentialUnit a ^ k).val).constantCoeff = 1 := by
  rw [exponentialUnit_zpow, exponentialUnit_val, constantCoeff_series]

/-- The nonzero linear coefficient makes `z exp(aX)` a local coordinate at `z`. -/
theorem order_polynomial_coordinate (P : Polynomial K) (hP : P ≠ 0)
    (z a : K) (hz : z ≠ 0) (ha : a ≠ 0) :
    (P.eval₂ PowerSeries.C (PowerSeries.C z * series a)).order =
      (P.rootMultiplicity z : ℕ∞) := by
  apply PolynomialCoordinateMultiplicity.order_eval_of_linear_ne_zero P hP z
  · simp
  · simpa only [PowerSeries.coeff_C_mul, coeff_one_series] using mul_ne_zero hz ha

end
end Surreal.FormalExponentialCoordinate
