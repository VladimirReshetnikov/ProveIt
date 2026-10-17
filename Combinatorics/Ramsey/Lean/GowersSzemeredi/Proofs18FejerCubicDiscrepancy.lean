import GowersSzemeredi.Proofs18GeneralPhaseInverseAssembly
import GowersSzemeredi.Proofs18FejerCubicParameters
import GowersSzemeredi.Proofs18FejerCubicTwistedDiscrepancy

/-! A fully explicit threshold for the cubic function inverse theorem.

`fejer_cubic_function_discrepancy_bound` and
`fejer_cubic_nonuniformity_discrepancy_partition` are in
`Proofs18FejerCubicDiscrepancySide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

def fejerCubicInverseThreshold (alpha : Real) : Real :=
  max (fejerCubicTwistedThreshold alpha)
    (positivePowerThreshold (fejerCubicPhaseRefinementConstant alpha) 1
      (fejerCubicDiscrepancyExponent alpha))

end LeanProofs.GowersSzemeredi
