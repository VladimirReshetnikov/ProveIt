import FabiusFunction.PeriodicRegularity

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

theorem fabiusFirstSaddleOddLinear_periodic :
    Function.Periodic fabiusFirstSaddleOddLinear 1 := by
  intro u
  unfold fabiusFirstSaddleOddLinear
  rw [negativeLaplacePsi_deriv_periodic u]

theorem fabiusFirstSaddleEvenQuadratic_periodic :
    Function.Periodic fabiusFirstSaddleEvenQuadratic 1 := by
  intro u
  unfold fabiusFirstSaddleEvenQuadratic
  rw [negativeLaplacePsi_deriv_periodic u,
    negativeLaplacePsi_secondDeriv_periodic u]

theorem fabiusFirstSaddleCorrection_periodic :
    Function.Periodic fabiusFirstSaddleCorrection 1 := by
  intro u
  unfold fabiusFirstSaddleCorrection
  rw [negativeLaplacePsi_deriv_periodic u,
    negativeLaplacePsi_secondDeriv_periodic u]

theorem continuous_fabiusFirstSaddleCorrection :
    Continuous fabiusFirstSaddleCorrection := by
  unfold fabiusFirstSaddleCorrection
  exact (continuous_const.add continuous_const).sub
    ((continuous_secondDeriv_negativeLaplacePsi.add
      (continuous_deriv_negativeLaplacePsi.pow 2)).div_const _)

theorem isBounded_range_fabiusFirstSaddleCorrection :
    Bornology.IsBounded (Set.range fabiusFirstSaddleCorrection) :=
  fabiusFirstSaddleCorrection_periodic.isBounded_of_continuous one_ne_zero
    continuous_fabiusFirstSaddleCorrection

end Fabius
