import FabiusFunction.AlgebraicInverseGermBinomial
import FabiusFunction.QuadraticCompositionalInverse

/-!
# The quarter Catalan germ as a rescaling of the dyadic quantile germ

The concrete dyadic quantile germ has parameter-normalized equation

`dyadicGermTwo + 4 * dyadicGermTwo ^ 2 = (4 / 9) * X`,

whereas the formal Taylor shadow of the actual inverse Fabius function at
`F(1 / 4) = 5 / 72` is the inverse of `X + 4 * X ^ 2`, hence solves the same
equation with right-hand side `X`.  Rescaling the parameter by `9 / 4`
identifies the two series exactly.

This file is purely formal and does not itself identify the analytic inverse
Fabius function with a convergent series on a neighborhood.  The downstream
module `FabiusInverseQuarterJet` proves equality of the actual derivative jet
with the quadratic inverse while retaining this nonanalytic boundary.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

/-- The distinguished dyadic germ satisfies its explicit quadratic equation. -/
theorem dyadicGermTwo_functionalEquation :
    dyadicGermTwo + 4 * dyadicGermTwo ^ 2 =
      PowerSeries.C ((4 : ℚ) / 9) * PowerSeries.X := by
  have h := eval_germRoot dyadicWeightsTwo dyadicJetTwo rfl
    dyadicJetTwo_coeff_zero
    (by rw [dyadicJetTwo_coeff_one]; exact isUnit_one)
  rw [germPolynomial_dyadicTwo_eval] at h
  exact sub_eq_zero.mp h

/-- Rescaling the dyadic parameter by `9 / 4` gives the Catalan reversion of
`X + 4 * X²`. -/
theorem rescale_dyadicGermTwo_eq_quadraticInverse :
    PowerSeries.rescale ((9 : ℚ) / 4) dyadicGermTwo =
      QuadraticInverse.inverse (4 : ℚ) := by
  apply QuadraticInverse.eq_inverse
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_germRoot _ _ _ _ _
  · have hC (q : ℚ) :
        PowerSeries.rescale ((9 : ℚ) / 4) (PowerSeries.C q) =
          PowerSeries.C q := by
      ext n
      simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
      split_ifs with hn
      · subst n
        simp
      · simp
    have h := congrArg (PowerSeries.rescale ((9 : ℚ) / 4))
      dyadicGermTwo_functionalEquation
    simp only [map_add, map_mul, map_pow, map_ofNat, hC,
      PowerSeries.rescale_X] at h
    have hfour : (4 : PowerSeries ℚ) = PowerSeries.C (4 : ℚ) :=
      (map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm
    rw [hfour] at h
    calc
      PowerSeries.rescale ((9 : ℚ) / 4) dyadicGermTwo +
          PowerSeries.C (4 : ℚ) *
            PowerSeries.rescale ((9 : ℚ) / 4) dyadicGermTwo ^ 2 =
          PowerSeries.C ((4 : ℚ) / 9) *
            (PowerSeries.C ((9 : ℚ) / 4) * PowerSeries.X) := h
      _ = PowerSeries.X := by
        rw [← mul_assoc, ← map_mul,
          show ((4 : ℚ) / 9) * ((9 : ℚ) / 4) = 1 by norm_num,
          map_one, one_mul]

/-- Equivalently, the dyadic germ is the quarter Catalan inverse with its
variable rescaled by `4 / 9`. -/
theorem dyadicGermTwo_eq_rescale_quadraticInverse :
    dyadicGermTwo =
      PowerSeries.rescale ((4 : ℚ) / 9)
        (QuadraticInverse.inverse (4 : ℚ)) := by
  calc
    dyadicGermTwo =
        PowerSeries.rescale ((4 : ℚ) / 9)
          (PowerSeries.rescale ((9 : ℚ) / 4) dyadicGermTwo) := by
      rw [PowerSeries.rescale_rescale]
      norm_num
    _ = PowerSeries.rescale ((4 : ℚ) / 9)
        (QuadraticInverse.inverse (4 : ℚ)) := by
      rw [rescale_dyadicGermTwo_eq_quadraticInverse]

/-- The report-facing Catalan normalization of every positive-degree dyadic
germ coefficient.  The extra power `(4 / 9)^(m + 1)` is exactly the parameter
rescaling that distinguishes the finite-spline germ from the unscaled quarter
inverse shadow. -/
@[simp]
theorem coeff_dyadicGermTwo_succ (m : ℕ) :
    PowerSeries.coeff (m + 1) dyadicGermTwo =
      ((4 : ℚ) / 9) ^ (m + 1) * (-4 : ℚ) ^ m * (catalan m : ℚ) := by
  rw [dyadicGermTwo_eq_rescale_quadraticInverse,
    PowerSeries.coeff_rescale, QuadraticInverse.coeff_succ_inverse]
  ring

end Fabius
