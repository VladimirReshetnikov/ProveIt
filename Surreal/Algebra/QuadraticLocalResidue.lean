import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Local Laurent residues of a quadratic denominator

The simple and collided residues in `trigonometry:thm:residuepairing`
and `trigonometry:eq:residuesum` are literal coefficients of formal
Laurent series. At a nonzero root `s`, polynomial translation gives the
local coordinate `W = s + T`; the denominator is `T * (2*s + T)`.
The power-series inverse of the second factor and the Laurent monomial
`T⁻¹` define the quotient. At the collision, the quotient is `T⁻²*g(T)`.
Multiplication by each actual translated denominator verifies the
quotient before its residue coefficient is computed.

These statements hold over any characteristic-zero field. Applications
to the actual surcomplex field require no analytic convergence premise.
-/

namespace Surreal.QuadraticLocalResidue

open Polynomial
open scoped PowerSeries LaurentSeries

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Expand the polynomial numerator in the actual local coordinate `W=s+T`. -/
def translatedSeries (s : K) (g : K[X]) : PowerSeries K :=
  (g.comp (X + C s) : K[X])

/-- The nonvanishing factor of the translated quadratic denominator. -/
def simpleUnitSeries (s : K) : PowerSeries K := PowerSeries.C (2 * s) + PowerSeries.X

/-- Invert the nonvanishing power-series factor using its actual unit constant coefficient. -/
def simpleUnitInverse (s : K) (hs : s ≠ 0) : PowerSeries K :=
  PowerSeries.invOfUnit (simpleUnitSeries s)
    (Units.mk0 (2 * s) (mul_ne_zero two_ne_zero hs))

/-- The genuine local Laurent quotient at a nonzero root. -/
def simpleQuotient (s : K) (hs : s ≠ 0) (g : K[X]) : K⸨X⸩ :=
  HahnSeries.single (-1) 1 *
    ((translatedSeries s g * simpleUnitInverse s hs : PowerSeries K) : K⸨X⸩)

omit [CharZero K] in
/-- The numerator's local constant coefficient is its evaluation at the center. -/
@[simp] theorem constantCoeff_translatedSeries (s : K) (g : K[X]) :
    PowerSeries.constantCoeff (translatedSeries s g) = g.eval s := by
  rw [translatedSeries, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]

/-- The formal inverse has the reciprocal constant coefficient. -/
@[simp] theorem constantCoeff_simpleUnitInverse (s : K) (hs : s ≠ 0) :
    PowerSeries.constantCoeff (simpleUnitInverse s hs) = (2 * s)⁻¹ := by
  simp [simpleUnitInverse]

/-- The chosen power series is an actual multiplicative inverse of the unit factor. -/
theorem simpleUnitSeries_mul_inverse (s : K) (hs : s ≠ 0) :
    simpleUnitSeries s * simpleUnitInverse s hs = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp [simpleUnitSeries]

omit [CharZero K] in
/-- Translating the quadratic denominator factors it into its local parameter and unit part. -/
theorem translated_quadratic (s : K) :
    translatedSeries s (X ^ 2 - C (s ^ 2)) = PowerSeries.X * simpleUnitSeries s := by
  have he : (X ^ 2 - C (s ^ 2) : K[X]).comp (X + C s) = X * (C (2 * s) + X) := by
    rw [Polynomial.sub_comp, Polynomial.X_pow_comp, Polynomial.C_comp,
      map_pow, map_mul, map_ofNat]
    ring
  rw [translatedSeries, he]
  simp only [Polynomial.coe_mul, Polynomial.coe_X,
    Polynomial.coe_add, Polynomial.coe_C, simpleUnitSeries]

/-- Multiplying the local quotient by the translated denominator recovers the numerator. -/
theorem denominator_mul_simpleQuotient (s : K) (hs : s ≠ 0) (g : K[X]) :
    ((translatedSeries s (X ^ 2 - C (s ^ 2)) : PowerSeries K) : K⸨X⸩) *
      simpleQuotient s hs g = ((translatedSeries s g : PowerSeries K) : K⸨X⸩) := by
  rw [translated_quadratic, PowerSeries.coe_mul, PowerSeries.coe_X, simpleQuotient]
  calc
    _ = (HahnSeries.single 1 (1 : K) * HahnSeries.single (-1) 1) *
        ((translatedSeries s g * (simpleUnitSeries s * simpleUnitInverse s hs) :
          PowerSeries K) : K⸨X⸩) := by
      simp only [PowerSeries.coe_mul]
      ring
    _ = _ := by
      rw [simpleUnitSeries_mul_inverse, mul_one]
      simp [HahnSeries.single_mul_single]

/-- The same quotient is verified for any specified quadratic parameter with root `s`. -/
theorem denominator_mul_simpleQuotient_of_sq_eq (d s : K) (hs : s ≠ 0)
    (hd : s ^ 2 = d) (g : K[X]) :
    ((translatedSeries s (X ^ 2 - C d) : PowerSeries K) : K⸨X⸩) *
      simpleQuotient s hs g = ((translatedSeries s g : PowerSeries K) : K⸨X⸩) := by
  rw [← hd]
  exact denominator_mul_simpleQuotient s hs g

/-- The negative-root quotient has the same global quadratic denominator. -/
theorem denominator_mul_negativeQuotient (s : K) (hs : s ≠ 0) (g : K[X]) :
    ((translatedSeries (-s) (X ^ 2 - C (s ^ 2)) : PowerSeries K) : K⸨X⸩) *
      simpleQuotient (-s) (neg_ne_zero.mpr hs) g =
        ((translatedSeries (-s) g : PowerSeries K) : K⸨X⸩) := by
  simpa only [neg_sq] using denominator_mul_simpleQuotient (-s) (neg_ne_zero.mpr hs) g

/-- The literal coefficient of `T⁻¹` is the usual simple residue `g(s)/(2*s)`. -/
theorem coeff_simpleQuotient (s : K) (hs : s ≠ 0) (g : K[X]) :
    (simpleQuotient s hs g).coeff (-1) = g.eval s / (2 * s) := by
  rw [simpleQuotient, HahnSeries.coeff_single_mul]
  norm_num only [sub_self, one_mul, PowerSeries.coeff_coe]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    constantCoeff_translatedSeries, constantCoeff_simpleUnitInverse, div_eq_mul_inv]
  simp only [if_false]

/-- The second simple residue retains the sign of the derivative at the negative root. -/
theorem coeff_negativeQuotient (s : K) (hs : s ≠ 0) (g : K[X]) :
    (simpleQuotient (-s) (neg_ne_zero.mpr hs) g).coeff (-1) = g.eval (-s) / (-2 * s) := by
  rw [coeff_simpleQuotient]
  congr 1
  ring

/-- The sum is the sum of two actual Laurent coefficients, with the displayed divided difference. -/
theorem simple_residues_sum (s : K) (hs : s ≠ 0) (g : K[X]) :
    (simpleQuotient s hs g).coeff (-1) +
      (simpleQuotient (-s) (neg_ne_zero.mpr hs) g).coeff (-1) =
        (g.eval s - g.eval (-s)) / (2 * s) := by
  rw [coeff_simpleQuotient, coeff_simpleQuotient, mul_neg, div_neg, sub_div]
  ring

/-- At the collided root the genuine quotient is the double Laurent pole times the polynomial. -/
def collisionQuotient (g : K[X]) : K⸨X⸩ :=
  HahnSeries.single (-2) 1 * ((g : PowerSeries K) : K⸨X⸩)

omit [CharZero K] in
/-- Multiplication by `T²` verifies the collision quotient directly. -/
theorem denominator_mul_collisionQuotient (g : K[X]) :
    (((X ^ 2 : K[X]) : PowerSeries K) : K⸨X⸩) * collisionQuotient g =
      ((g : PowerSeries K) : K⸨X⸩) := by
  rw [Polynomial.coe_pow, Polynomial.coe_X, PowerSeries.coe_pow, PowerSeries.coe_X,
    HahnSeries.single_pow, collisionQuotient, ← mul_assoc, HahnSeries.single_mul_single]
  norm_num

omit [CharZero K] in
/-- The collision residue is exactly the linear coefficient of the original polynomial. -/
theorem coeff_collisionQuotient (g : K[X]) :
    (collisionQuotient g).coeff (-1) = g.coeff 1 := by
  rw [collisionQuotient, HahnSeries.coeff_single_mul]
  norm_num [PowerSeries.coeff_coe, Polynomial.coeff_coe]

omit [CharZero K] in
/-- The literal Laurent residue at the double root is `g'(0)`. -/
theorem coeff_collisionQuotient_eq_derivative (g : K[X]) :
    (collisionQuotient g).coeff (-1) = g.derivative.eval 0 := by
  rw [coeff_collisionQuotient, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  simp

end
end Surreal.QuadraticLocalResidue
