import GowersSzemeredi.Proofs18GeneralLocalInverseAssembly
import GowersSzemeredi.Proofs18FejerCubicParameters
import GowersSzemeredi.Proofs18FejerCubicAt

/-! Explicit modulus threshold for the global cubic twisted discrepancy partition.

`fejer_cubic_nonuniformity_twisted_discrepancy` is in
`Proofs18FejerCubicTwistedDiscrepancySide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

def fejerCubicTwistedThreshold (alpha : Real) : Real :=
  fejerCubicPrimeModelThreshold alpha
    (max 4 (quadraticExponentialThreshold (fejerCubicLocalQuadraticParameter alpha)))

end LeanProofs.GowersSzemeredi
