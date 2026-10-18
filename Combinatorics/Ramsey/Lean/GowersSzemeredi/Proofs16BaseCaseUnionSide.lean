import GowersSzemeredi.Proofs16BaseCaseUnion

/-! Declarations of `Proofs16BaseCaseUnion` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

/-- The repaired finite-union closure used by the one-dimensional base-case
assembly. -/
theorem properUnionClosure_holds : ProperUnionClosure := by
  intro N d r _ gamma s Gamma hr hs hGamma
  exact properMultiplyLinear_finsetUnion gamma s hs Gamma hr hGamma

end LeanProofs.GowersSzemeredi.BaseCase
