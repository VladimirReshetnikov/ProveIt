import GowersSzemeredi.Proofs10Regular
import GowersSzemeredi.ComponentTradeoffSide

/-! Declarations of `Proofs10Regular` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators ZMod ENNReal
open Finset Set MeasureTheory

namespace LeanProofs.GowersSzemeredi

/-- The original square-root clause is valid under the same inherited setup. -/
theorem lemma_10_5_original_sqrt_holds : lemma_10_5_original_sqrt := by
  intro N _ X _ _ D phi B alpha rho M sigma eta x hsetup hsigmaAlpha
    hanchor hrho hrhoAlpha hrhoAlphaSq hsigmaRho
  obtain ⟨W, hW⟩ := lemma_10_5_all_tradeoffs_holds N X D phi B alpha rho M
    sigma eta x hsetup hsigmaAlpha hanchor hrho hrhoAlpha hrhoAlphaSq hsigmaRho
  exact ⟨W, hW (1 / 2)⟩

end LeanProofs.GowersSzemeredi
