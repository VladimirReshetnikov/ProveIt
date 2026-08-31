import FabiusFunction.FabiusLambertPhaseExtraction
import FabiusFunction.LambertPhaseLockedBell

/-!
# Bell forms of the phase-locked Fabius residual expansion

`FabiusLambertPhaseExtraction` expresses each exact residual contribution
through a complete homogeneous evaluation on the shifted reciprocal alphabet.
This module rewrites that algebraic factor using the complete Bell polynomial
identity from `LambertPhaseLockedBell`.

No asymptotic statement is changed: the results below are exact reformulations
of the existing residual term and its finite partial sum.

## Main results

* `fabiusPhaseLockedResidualTerm_eq_bell` is the Bell-polynomial form of one
  exact residual contribution.
* `fabiusPhaseLockedResidualPartialSum_eq_sum_bell` rewrites every summand in
  the exact finite residual partial sum.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

noncomputable section

/-- One exact phase-locked residual contribution, with its complete
homogeneous factor rewritten as the factorially normalized complete Bell
polynomial of the shifted reciprocal power sums. -/
theorem fabiusPhaseLockedResidualTerm_eq_bell
    (r n : ℕ) (lambda : ℝ) :
    fabiusPhaseLockedResidualTerm r n lambda =
      (-1 : ℝ) ^ r *
        (∏ j ∈ range (r + 1), (lambda + (j : ℝ))⁻¹) *
        factorialNormalize
          (completeBellPolynomial (shiftedReciprocalBellInput lambda r)) n *
        fabiusSaddleLogCoefficient (r + 1 + n) lambda := by
  unfold fabiusPhaseLockedResidualTerm
  rw [completeHomogeneousEvalOn_shiftedReciprocal_eq_bell]

/-- The first `S` exact phase-locked residual contributions, with every
complete homogeneous factor rewritten in complete-Bell form. -/
theorem fabiusPhaseLockedResidualPartialSum_eq_sum_bell
    (r S : ℕ) (lambda : ℝ) :
    fabiusPhaseLockedResidualPartialSum r S lambda =
      ∑ n ∈ range S,
        (-1 : ℝ) ^ r *
          (∏ j ∈ range (r + 1), (lambda + (j : ℝ))⁻¹) *
          factorialNormalize
            (completeBellPolynomial (shiftedReciprocalBellInput lambda r)) n *
          fabiusSaddleLogCoefficient (r + 1 + n) lambda := by
  unfold fabiusPhaseLockedResidualPartialSum
  apply Finset.sum_congr rfl
  intro n hn
  exact fabiusPhaseLockedResidualTerm_eq_bell r n lambda

end

end Fabius
