import GowersSzemeredi.Proofs16BaseCaseUnion

/-!
# Repaired endpoint for Lemma 16.3

This module closes the isolated one-dimensional base-case chain.  Catalogue
migration is intentionally deferred until the repaired shared predicates are
in place.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi.BaseCase

/-- The faithful one-dimensional base case, assembled from the repaired
finite-union closure. -/
theorem proper_lemma_16_3_holds : ProperTheorem162At 1 :=
  proper_lemma_16_3_of_unionClosure properUnionClosure_holds

end LeanProofs.GowersSzemeredi.BaseCase
