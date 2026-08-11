import PolynomialFormulas.LazardInvariantMolienCoefficients

/-!
# The `F20` Molien numerator as a formal power-series identity

`LazardInvariantMolienCoefficients` proves the honest coefficientwise Molien
formula and rewrites the resulting Hilbert series as the four cycle-type
geometric series.  This file performs the remaining algebra *inside formal
power series*.  Thus the numerator

`1 + X^4 + X^5 + X^6 + X^7 + X^8`

is connected directly to the invariant dimensions, rather than merely to a
separate identity in rational functions.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantMolienNumeratorSeries

open LeanProofs.PolynomialFormulas.LazardInvariantMolienCoefficients

set_option autoImplicit false

noncomputable section

abbrev RationalPowerSeries := PowerSeries ℚ

/-- The factor `1-X^m`. -/
def stepDenominator (m : ℕ) : RationalPowerSeries :=
  1 - PowerSeries.X ^ m

/-- `1+X`, the quotient `(1-X^2)/(1-X)`. -/
def quotientTwo : RationalPowerSeries :=
  1 + PowerSeries.X

/-- `1+X+X^2`, the quotient `(1-X^3)/(1-X)`. -/
def quotientThree : RationalPowerSeries :=
  1 + PowerSeries.X + PowerSeries.X ^ 2

/-- `1+X^2`, the quotient `(1-X^4)/(1-X^2)`. -/
def quotientFour : RationalPowerSeries :=
  1 + PowerSeries.X ^ 2

/-- `1+X+X^2+X^3+X^4`, the quotient `(1-X^5)/(1-X)`. -/
def quotientFive : RationalPowerSeries :=
  1 + PowerSeries.X + PowerSeries.X ^ 2 +
    PowerSeries.X ^ 3 + PowerSeries.X ^ 4

/-- The denominator contributed by the five elementary symmetric
generators, whose degrees are `1,2,3,4,5`. -/
def symmetricDenominatorSeries : RationalPowerSeries :=
  stepDenominator 1 * stepDenominator 2 * stepDenominator 3 *
    stepDenominator 4 * stepDenominator 5

/-- Lazard's six-term numerator, now regarded as a formal power series. -/
def f20MolienNumeratorSeries : RationalPowerSeries :=
  1 + PowerSeries.X ^ 4 + PowerSeries.X ^ 5 +
    PowerSeries.X ^ 6 + PowerSeries.X ^ 7 + PowerSeries.X ^ 8

theorem stepDenominator_two :
    stepDenominator 2 = stepDenominator 1 * quotientTwo := by
  simp [stepDenominator, quotientTwo]
  ring

theorem stepDenominator_three :
    stepDenominator 3 = stepDenominator 1 * quotientThree := by
  simp [stepDenominator, quotientThree]
  ring

theorem stepDenominator_four :
    stepDenominator 4 = stepDenominator 2 * quotientFour := by
  simp [stepDenominator, quotientFour]
  ring

theorem stepDenominator_five :
    stepDenominator 5 = stepDenominator 1 * quotientFive := by
  simp [stepDenominator, quotientFive]
  ring

theorem geometricStepSeries_mul_stepDenominator (m : ℕ) (hm : m ≠ 0) :
    geometricStepSeries m * stepDenominator m = 1 := by
  simpa [stepDenominator] using
    geometricStepSeries_mul_one_sub_X_pow m hm

/-- A factorization adapted to cancelling the identity contribution. -/
theorem symmetricDenominatorSeries_identity_factorization :
    symmetricDenominatorSeries =
      stepDenominator 1 ^ 5 * quotientTwo ^ 2 * quotientThree *
        quotientFour * quotientFive := by
  rw [symmetricDenominatorSeries, stepDenominator_two,
    stepDenominator_three, stepDenominator_four,
    stepDenominator_five, stepDenominator_two]
  ring

/-- A factorization adapted to the `1 2^2` contribution. -/
theorem symmetricDenominatorSeries_twoTwo_factorization :
    symmetricDenominatorSeries =
      stepDenominator 1 * stepDenominator 2 ^ 2 *
        stepDenominator 3 * quotientFour * stepDenominator 5 := by
  rw [symmetricDenominatorSeries, stepDenominator_four]
  ring

theorem identityContribution_mul_denominator :
    geometricStepSeries 1 ^ 5 * symmetricDenominatorSeries =
      quotientTwo ^ 2 * quotientThree * quotientFour * quotientFive := by
  rw [symmetricDenominatorSeries_identity_factorization]
  have h := geometricStepSeries_mul_stepDenominator 1 (by decide)
  calc
    geometricStepSeries 1 ^ 5 *
        (stepDenominator 1 ^ 5 * quotientTwo ^ 2 * quotientThree *
          quotientFour * quotientFive) =
      (geometricStepSeries 1 * stepDenominator 1) ^ 5 *
        quotientTwo ^ 2 * quotientThree * quotientFour * quotientFive := by
          ring
    _ = quotientTwo ^ 2 * quotientThree * quotientFour * quotientFive := by
      rw [h]
      simp

theorem fiveCycleContribution_mul_denominator :
    geometricStepSeries 5 * symmetricDenominatorSeries =
      stepDenominator 1 * stepDenominator 2 * stepDenominator 3 *
        stepDenominator 4 := by
  have h := geometricStepSeries_mul_stepDenominator 5 (by decide)
  rw [symmetricDenominatorSeries]
  calc
    geometricStepSeries 5 *
        (stepDenominator 1 * stepDenominator 2 * stepDenominator 3 *
          stepDenominator 4 * stepDenominator 5) =
      (geometricStepSeries 5 * stepDenominator 5) *
        (stepDenominator 1 * stepDenominator 2 * stepDenominator 3 *
          stepDenominator 4) := by
            ring
    _ = stepDenominator 1 * stepDenominator 2 * stepDenominator 3 *
        stepDenominator 4 := by
      rw [h]
      simp

theorem twoTwoContribution_mul_denominator :
    (geometricStepSeries 1 * geometricStepSeries 2 ^ 2) *
        symmetricDenominatorSeries =
      stepDenominator 3 * quotientFour * stepDenominator 5 := by
  rw [symmetricDenominatorSeries_twoTwo_factorization]
  have h1 := geometricStepSeries_mul_stepDenominator 1 (by decide)
  have h2 := geometricStepSeries_mul_stepDenominator 2 (by decide)
  calc
    (geometricStepSeries 1 * geometricStepSeries 2 ^ 2) *
        (stepDenominator 1 * stepDenominator 2 ^ 2 *
          stepDenominator 3 * quotientFour * stepDenominator 5) =
      (geometricStepSeries 1 * stepDenominator 1) *
        (geometricStepSeries 2 * stepDenominator 2) ^ 2 *
        (stepDenominator 3 * quotientFour * stepDenominator 5) := by
          ring
    _ = stepDenominator 3 * quotientFour * stepDenominator 5 := by
      rw [h1, h2]
      simp

theorem fourCycleContribution_mul_denominator :
    (geometricStepSeries 1 * geometricStepSeries 4) *
        symmetricDenominatorSeries =
      stepDenominator 2 * stepDenominator 3 * stepDenominator 5 := by
  have h1 := geometricStepSeries_mul_stepDenominator 1 (by decide)
  have h4 := geometricStepSeries_mul_stepDenominator 4 (by decide)
  rw [symmetricDenominatorSeries]
  calc
    (geometricStepSeries 1 * geometricStepSeries 4) *
        (stepDenominator 1 * stepDenominator 2 * stepDenominator 3 *
          stepDenominator 4 * stepDenominator 5) =
      (geometricStepSeries 1 * stepDenominator 1) *
        (geometricStepSeries 4 * stepDenominator 4) *
        (stepDenominator 2 * stepDenominator 3 * stepDenominator 5) := by
          ring
    _ = stepDenominator 2 * stepDenominator 3 * stepDenominator 5 := by
      rw [h1, h4]
      simp

/-- The finite polynomial simplification at the end of the class-sum
calculation. -/
theorem reducedClassSum_eq_numerator :
    PowerSeries.C (20 : ℚ)⁻¹ *
        (quotientTwo ^ 2 * quotientThree * quotientFour * quotientFive +
          PowerSeries.C 4 *
            (stepDenominator 1 * stepDenominator 2 * stepDenominator 3 *
              stepDenominator 4) +
          PowerSeries.C 5 *
            (stepDenominator 3 * quotientFour * stepDenominator 5) +
          PowerSeries.C 10 *
            (stepDenominator 2 * stepDenominator 3 * stepDenominator 5)) =
      f20MolienNumeratorSeries := by
  simp [stepDenominator, quotientTwo, quotientThree, quotientFour,
    quotientFive, f20MolienNumeratorSeries]
  rw [map_ofNat (PowerSeries.C : ℚ →+* RationalPowerSeries) 4,
    map_ofNat (PowerSeries.C : ℚ →+* RationalPowerSeries) 5,
    map_ofNat (PowerSeries.C : ℚ →+* RationalPowerSeries) 10]
  have hc :
      PowerSeries.C ((20 : ℚ)⁻¹) * (20 : RationalPowerSeries) = 1 := by
    rw [← map_ofNat (PowerSeries.C : ℚ →+* RationalPowerSeries) 20,
      ← map_mul]
    norm_num
  calc
    _ = (PowerSeries.C ((20 : ℚ)⁻¹) * 20) *
        (1 + PowerSeries.X ^ 4 + PowerSeries.X ^ 5 +
          PowerSeries.X ^ 6 + PowerSeries.X ^ 7 +
          PowerSeries.X ^ 8) := by ring
    _ = _ := by rw [hc]; simp

/-- The honest `F20` invariant Hilbert series has Lazard's numerator after
multiplication by the symmetric denominator. -/
theorem f20InvariantHilbertSeries_mul_symmetricDenominator :
    f20InvariantHilbertSeries * symmetricDenominatorSeries =
      f20MolienNumeratorSeries := by
  rw [f20InvariantHilbertSeries_eq_geometric_class_sum]
  calc
    (PowerSeries.C (20 : ℚ)⁻¹ *
        (geometricStepSeries 1 ^ 5 +
          PowerSeries.C 4 * geometricStepSeries 5 +
          PowerSeries.C 5 *
            (geometricStepSeries 1 * geometricStepSeries 2 ^ 2) +
          PowerSeries.C 10 *
            (geometricStepSeries 1 * geometricStepSeries 4))) *
          symmetricDenominatorSeries =
      PowerSeries.C (20 : ℚ)⁻¹ *
        (geometricStepSeries 1 ^ 5 * symmetricDenominatorSeries +
          PowerSeries.C 4 *
            (geometricStepSeries 5 * symmetricDenominatorSeries) +
          PowerSeries.C 5 *
            ((geometricStepSeries 1 * geometricStepSeries 2 ^ 2) *
              symmetricDenominatorSeries) +
          PowerSeries.C 10 *
            ((geometricStepSeries 1 * geometricStepSeries 4) *
              symmetricDenominatorSeries)) := by
        ring
    _ = PowerSeries.C (20 : ℚ)⁻¹ *
        (quotientTwo ^ 2 * quotientThree * quotientFour * quotientFive +
          PowerSeries.C 4 *
            (stepDenominator 1 * stepDenominator 2 * stepDenominator 3 *
              stepDenominator 4) +
          PowerSeries.C 5 *
            (stepDenominator 3 * quotientFour * stepDenominator 5) +
          PowerSeries.C 10 *
            (stepDenominator 2 * stepDenominator 3 * stepDenominator 5)) := by
      rw [identityContribution_mul_denominator,
        fiveCycleContribution_mul_denominator,
        twoTwoContribution_mul_denominator,
        fourCycleContribution_mul_denominator]
    _ = f20MolienNumeratorSeries := reducedClassSum_eq_numerator

end

end LeanProofs.PolynomialFormulas.LazardInvariantMolienNumeratorSeries
