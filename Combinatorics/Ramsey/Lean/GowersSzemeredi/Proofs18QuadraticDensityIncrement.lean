import GowersSzemeredi.Proofs18QuadraticDiscrepancy
import GowersSzemeredi.Proofs18QuantitativeSzemeredi
import GowersSzemeredi.Proofs03ProgressionCount

/-! The alias `balanced_discValued` of `cor33_balanced_discValued`.

The unconditional quadratic density increment
(`density_increment_of_discrepancy_partition`: the size exponent and density
gain are explicit, the sufficiently-large threshold is existential) is in
`Proofs18QuadraticDensityIncrementSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

alias balanced_discValued := cor33_balanced_discValued

end LeanProofs.GowersSzemeredi
