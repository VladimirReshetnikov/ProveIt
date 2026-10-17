import GowersSzemeredi.Proofs16Lemma5
import GowersSzemeredi.Proofs16RadiusComparison

/-! Declarations of `Proofs16Lemma5` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- The printed parameters satisfy the hypotheses: `lemma_16_5_with` contains
the printed Lemma 16.5's conclusion. -/
theorem lemma_16_5_with_printed_hyps {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16ThetaOne theta gamma k / 4 ∧ section16ThetaOne theta gamma k / 4 ≤ 1 / 36 ∧
      ∀ alpha : Real, section16ThetaOne theta gamma k / 4 ≤ alpha → alpha ≤ 1 / 6 →
        section16Zeta theta gamma k ≤ section10Zeta alpha := by
  obtain ⟨h0, h1⟩ := section16_density_parameter_bounds k ht ht1 hg hg1
  exact ⟨h0, h1, fun alpha ha ha1 => section16_zeta_le_section10Zeta k ht ht1 hg hg1 ha ha1⟩

/-- Exact companion for Lemma 16.5. -/
theorem lemma_16_5_holds : lemma_16_5 := by
  intro N k _ theta gamma B phi ht ht1 hg hg1 hB
  have hp := lemma_16_5_with_printed_hyps k ht ht1 hg hg1
  exact lemma_16_5_with _ _ B phi hp.1 hp.2.1 hp.2.2 hB.2

end LeanProofs.GowersSzemeredi
