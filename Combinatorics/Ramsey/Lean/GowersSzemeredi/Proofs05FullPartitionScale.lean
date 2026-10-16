import GowersSzemeredi.Proofs05FullPartition
import GowersSzemeredi.Proofs05Corollary58

/-! Corollary 5.8 with an explicit scale, from Corollary 5.6. Kept apart from `Proofs05FullPartition` so that the final route does not import `Proofs05Corollary58`. -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The explicitly scale-qualified repair of Corollary 5.8. This is not a
proof of the catalogue statement without its missing scale hypothesis. -/
theorem corollary_5_8_with_scale_holds : corollary_5_8_with_scale :=
  corollary_5_8_with_scale_holds_of_corollary_5_6 corollary_5_6_holds

end LeanProofs.GowersSzemeredi
