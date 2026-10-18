import GowersSzemeredi.Proofs16LiftWidth
import GowersSzemeredi.Proofs16BaseCaseUnion

/-! # The verified local affine lift at every input scale

`section16_local_affine_lift_all_scales` and `section16_slice_control_ranges`
are in `Proofs16LiftAllScalesSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

alias isMultilinear_constant := BaseCase.isMultilinear_const

end LeanProofs.GowersSzemeredi
