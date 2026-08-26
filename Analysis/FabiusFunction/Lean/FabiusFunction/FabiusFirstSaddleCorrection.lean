import FabiusFunction.FabiusSaddleCoefficientRecurrence

/-!
# The first periodic saddle correction for the Fabius function

The leading corrected asymptotic retains the centered periodic function
`negativeLaplacePsi` at the exact lower-Lambert phase.  Expanding the
normalized Bromwich kernel one order further gives a periodic coefficient of
`1 / lambda`.  This module records that coefficient independently of the
analytic remainder estimate which promotes it to an asymptotic theorem.

Writing `L = log 2`, `A = Psi' / L - 1/2`, and

`B = -1/4 + 1/(2L) + Psi'/(2L) - Psi''/(2L^2)`,

the first two exponent polynomials are

`P₁(v) = i (A v + v^3/3)` and `P₂(v) = v^4/4 + B v^2`.

Gaussian contraction uses the moments `(E v^2, E v^4, E v^6) =
(1,3,15)`.  Consequently the coefficient of both the relative mass and its
logarithm is

`1/24 + 1/(2L) - (Psi'' + (Psi')^2)/(2L^2)`.
-/

set_option autoImplicit false

namespace Fabius

/-- Coefficient of `v` in the first odd saddle polynomial. -/
noncomputable def fabiusFirstSaddleOddLinear (u : ℝ) : ℝ :=
  deriv negativeLaplacePsi u / Real.log 2 - 1 / 2

/-- Coefficient of `v^2` in the second saddle polynomial. -/
noncomputable def fabiusFirstSaddleEvenQuadratic (u : ℝ) : ℝ :=
  -1 / 4 + 1 / (2 * Real.log 2) +
    deriv negativeLaplacePsi u / (2 * Real.log 2) -
      deriv (deriv negativeLaplacePsi) u / (2 * (Real.log 2) ^ 2)

/-- The first periodic coefficient after the sharp Lambert main term.

The full logarithmic expansion begins

`log F(x) = fabiusSharpLambertMain x +
  fabiusFirstSaddleCorrection (fabiusLambertPhase x) /
    fabiusLambertPhase x + ...`.
-/
noncomputable def fabiusFirstSaddleCorrection (u : ℝ) : ℝ :=
  1 / 24 + 1 / (2 * Real.log 2) -
    (deriv (deriv negativeLaplacePsi) u +
      (deriv negativeLaplacePsi u) ^ 2) /
        (2 * (Real.log 2) ^ 2)

/-- Gaussian contraction of the first two exponent polynomials gives the
closed formula `fabiusFirstSaddleCorrection`. -/
theorem fabiusFirstSaddleCorrection_eq_gaussian_contraction (u : ℝ) :
    fabiusFirstSaddleCorrection u =
      3 / 4 + fabiusFirstSaddleEvenQuadratic u -
        (1 / 2) * (fabiusFirstSaddleOddLinear u ^ 2 +
          2 * fabiusFirstSaddleOddLinear u + 5 / 3) := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold fabiusFirstSaddleCorrection fabiusFirstSaddleEvenQuadratic
    fabiusFirstSaddleOddLinear
  field_simp [hL]
  ring

/-- The odd linear saddle coefficient is the zeroth bounded exponent jet. -/
theorem fabiusFirstSaddleOddLinear_eq_boundedExponentJet_zero (u : ℝ) :
    fabiusFirstSaddleOddLinear u =
      negativeLaplaceBoundedExponentJet 0 u := by
  simp [fabiusFirstSaddleOddLinear]

/-- The even quadratic saddle coefficient is negative one half of the first
bounded exponent jet. -/
theorem fabiusFirstSaddleEvenQuadratic_eq_neg_half_boundedExponentJet_one
    (u : ℝ) :
    fabiusFirstSaddleEvenQuadratic u =
      -negativeLaplaceBoundedExponentJet 1 u / 2 := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [negativeLaplaceBoundedExponentJet_one]
  unfold fabiusFirstSaddleEvenQuadratic
  field_simp [hL]
  ring

/-- In bounded exponent jets, the first saddle correction is
`-d₀^2 / 2 - d₀ - d₁ / 2 - 1 / 12`. -/
theorem fabiusFirstSaddleCorrection_eq_boundedExponentJets (u : ℝ) :
    fabiusFirstSaddleCorrection u =
      -negativeLaplaceBoundedExponentJet 0 u ^ 2 / 2 -
        negativeLaplaceBoundedExponentJet 0 u -
        negativeLaplaceBoundedExponentJet 1 u / 2 - 1 / 12 := by
  rw [fabiusFirstSaddleCorrection_eq_gaussian_contraction,
    fabiusFirstSaddleOddLinear_eq_boundedExponentJet_zero,
    fabiusFirstSaddleEvenQuadratic_eq_neg_half_boundedExponentJet_one]
  ring

/-- The odd linear saddle coefficient is one-periodic. -/
theorem fabiusFirstSaddleOddLinear_periodic :
    Function.Periodic fabiusFirstSaddleOddLinear 1 := by
  intro u
  unfold fabiusFirstSaddleOddLinear
  rw [negativeLaplacePsi_deriv_periodic u]

/-- The even quadratic saddle coefficient is one-periodic. -/
theorem fabiusFirstSaddleEvenQuadratic_periodic :
    Function.Periodic fabiusFirstSaddleEvenQuadratic 1 := by
  intro u
  unfold fabiusFirstSaddleEvenQuadratic
  rw [negativeLaplacePsi_deriv_periodic u,
    negativeLaplacePsi_secondDeriv_periodic u]

/-- The first saddle correction is one-periodic. -/
theorem fabiusFirstSaddleCorrection_periodic :
    Function.Periodic fabiusFirstSaddleCorrection 1 := by
  intro u
  unfold fabiusFirstSaddleCorrection
  rw [negativeLaplacePsi_deriv_periodic u,
    negativeLaplacePsi_secondDeriv_periodic u]

/-- The first saddle correction is continuous. -/
theorem continuous_fabiusFirstSaddleCorrection :
    Continuous fabiusFirstSaddleCorrection := by
  unfold fabiusFirstSaddleCorrection
  exact (continuous_const.add continuous_const).sub
    ((continuous_secondDeriv_negativeLaplacePsi.add
      (continuous_deriv_negativeLaplacePsi.pow 2)).div_const _)

/-- The first saddle correction has globally bounded range. -/
theorem isBounded_range_fabiusFirstSaddleCorrection :
    Bornology.IsBounded (Set.range fabiusFirstSaddleCorrection) :=
  fabiusFirstSaddleCorrection_periodic.isBounded_of_continuous one_ne_zero
    continuous_fabiusFirstSaddleCorrection

end Fabius
