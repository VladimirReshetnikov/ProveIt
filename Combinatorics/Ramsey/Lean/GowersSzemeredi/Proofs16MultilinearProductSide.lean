import GowersSzemeredi.Proofs16MultilinearProduct
import GowersSzemeredi.Proofs16ProductEndpointSide

/-! Declarations of `Proofs16MultilinearProduct` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- Exact full-domain endpoint equivalence, independent of the quantitative
induction and the invalid packaged branch-cover implication. -/
theorem section16_unit_product_iff_multilinear {N k : Nat} [NeZero N] [Fact N.Prime]
    (phi : Point N k → ZMod N) :
    HasProductProperty Finset.univ phi 1 ↔ IsMultilinear phi :=
  ⟨HasProductProperty.unit_multilinear, IsMultilinear.unit_productProperty⟩

end LeanProofs.GowersSzemeredi
