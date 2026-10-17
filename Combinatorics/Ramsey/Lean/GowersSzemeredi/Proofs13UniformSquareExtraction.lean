import GowersSzemeredi.Proofs13UniformSquareScale
import GowersSzemeredi.Proofs13UniformDensityRecurrence
import GowersSzemeredi.Proofs13UniformDensityBudgets

/-! Complete common-step square extraction with a density-uniform threshold.

`section13_complete_square_extraction_explicit` and
`section13_complete_square_extraction_uniform_density` are in
`Proofs13UniformSquareExtractionSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

def section13GeometricThreshold (delta : Real) : Real :=
  let c := section13Zeta delta / 2
  let e := (1 : Real) / (2 : Real) ^ (13 * section13Q delta)
  let f := (2 : Real) ^ (-(100 : Int)) * delta ^ 448
  let g := cor711Exponent ((2 : Real) ^ (-(135 : Int)) * delta ^ 704) 1
  max 1 (max (section13DensityRecurrenceThreshold delta)
    (max (section13DensityIntegerThreshold delta)
      (max (squareScaleThreshold c e f g ((2 : Real) ^ 135 * delta ^ (-(704 : Int))))
        (squarePowerThreshold c e f g))))

end LeanProofs.GowersSzemeredi
