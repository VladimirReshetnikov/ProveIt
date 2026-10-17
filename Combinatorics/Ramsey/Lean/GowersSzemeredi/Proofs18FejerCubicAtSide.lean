import GowersSzemeredi.Proofs18FejerCubicAt
import GowersSzemeredi.Proofs13FejerFourierExtractionSide

/-! Declarations of `Proofs18FejerCubicAt` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open scoped BigOperators

/-- The corpus extraction is an instance. -/
theorem fejerSquareAt_corpus {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    FejerSquareAt alpha (section13SquareExponent ((alpha / 2) ^ (4207554485 : Nat)))
      (section13FourierThreshold alpha) :=
  theorem_13_12_fejer_extraction_explicit alpha hα hαone

end

end LeanProofs.GowersSzemeredi
