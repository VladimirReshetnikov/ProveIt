import GowersSzemeredi.Proofs16BaseCaseUnion

/-!
# Repaired endpoint for Lemma 16.3

This module closes the one-dimensional base-case chain. The shared catalogue
uses proper boxes and loss parameters in `(0,1]`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi.BaseCase

/-- The faithful one-dimensional base case, assembled from the repaired
finite-union closure. -/
theorem proper_lemma_16_3_holds : ProperTheorem162At 1 :=
  proper_lemma_16_3_of_unionClosure properUnionClosure_holds

end LeanProofs.GowersSzemeredi.BaseCase

namespace LeanProofs.GowersSzemeredi

/-- Lemma 16.3 under the shared proper-box definition of multiple linearity. -/
theorem lemma_16_3_holds : lemma_16_3 := BaseCase.proper_lemma_16_3_holds

end LeanProofs.GowersSzemeredi
