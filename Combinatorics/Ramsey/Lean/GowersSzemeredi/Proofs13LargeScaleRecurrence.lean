import GowersSzemeredi.Proofs13QuadraticPartition
import GowersSzemeredi.Proofs13ExponentMargins
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The numerical hypotheses of quadratic recurrence hold uniformly at
large N. This constructs the preceding stages needed by bilinear extraction.

`eventually_floor_progression_length_ge`, `lemma_13_5_large_N`,
`section13_bilinear_extraction_from_context`,
`section13_eventually_initial_recurrence_scale`,
`section13_eventually_recurrence_scale` and `section13_uniform_recurrence_scale`
are in `Proofs13LargeScaleRecurrenceSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
open Filter
namespace LeanProofs.GowersSzemeredi

/-- Sufficient progression-size conditions for the checked quadratic
recurrence and its endpoint deletion. -/
def Section13RecurrenceScale (alpha : Real) (q L : Nat) : Prop :=
  simultaneousPolynomialThreshold 2 q < L ∧
  8 ≤ (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q)) ∧
  160 + 2 * alpha ^ 32 ≤ alpha ^ 32 * (L : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * q))

/-- The common edge Fourier cutoff is admissible for the proved initial
progression theorem. -/
theorem section13_lambda_le_initial_threshold {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    section10Lambda (alpha ^ 32 / 16) ≤ alpha ^ 32 / 4 := by
  rw [section13_lambda_formula hα]
  have hp : alpha ^ 176 ≤ alpha ^ 32 := pow_le_pow_of_le_one hα.le hαone (by omega)
  have hc : (2 : Real) ^ (-(59 : Int)) ≤ 1 / 4 := by norm_num
  calc
    _ ≤ (1 / 4 : Real) * alpha ^ 32 :=
      mul_le_mul hc hp (pow_nonneg hα.le _) (by norm_num)
    _ = _ := by ring

end LeanProofs.GowersSzemeredi
