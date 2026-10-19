import GowersSzemeredi.Proofs18IntervalUniformStopping
import GowersSzemeredi.Proofs18NaturalIntervalIncrement

/-! A quantitative four-term progression/density-increment alternative on
ordinary intervals. The density parameter stays relative to the interval.

`interval_quadratic_dichotomy` is in `Proofs18IntervalQuadraticDichotomySide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A uniformity parameter sufficient for the relative interval count. -/
def intervalQuadraticUniformityParameter (delta : Real) : Real :=
  (delta ^ 4 / 32768) ^ 8

theorem intervalQuadraticUniformityParameter_pos {delta : Real} (hδ : 0 < delta) :
    0 < intervalQuadraticUniformityParameter delta := by
  unfold intervalQuadraticUniformityParameter
  positivity

theorem intervalQuadraticUniformityParameter_le_one {delta : Real}
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) : intervalQuadraticUniformityParameter delta ≤ 1 := by
  have hp : delta ^ 4 ≤ 1 := pow_le_one₀ hδ hδone
  apply pow_le_one₀ (by positivity)
  linarith

end LeanProofs.GowersSzemeredi
