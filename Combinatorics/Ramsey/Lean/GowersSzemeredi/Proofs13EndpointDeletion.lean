import GowersSzemeredi.Proofs13QuadraticRecurrence
import GowersSzemeredi.Proofs16Slicing

/-! This module keeps `ModAP.interior`, `ModAP.interior_neighbors` and
`stage135AmbientQuadratic`; the rest of the development, with its description,
is in `Proofs13EndpointDeletionSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A quadratic polynomial in the ambient height variable. -/
def stage135AmbientQuadratic {N : Nat} (a b h : ZMod N) : ZMod N :=
  a * (4 : ZMod N)⁻¹ * h ^ 2 + b * (2 : ZMod N)⁻¹ * h

end LeanProofs.GowersSzemeredi
