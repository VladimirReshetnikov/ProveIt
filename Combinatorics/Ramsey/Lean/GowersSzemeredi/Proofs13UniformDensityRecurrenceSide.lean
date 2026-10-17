import GowersSzemeredi.Proofs13UniformDensityRecurrence
import GowersSzemeredi.Proofs13QuadraticPartitionSide

/-! Declarations of `Proofs13UniformDensityRecurrence` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open Filter

/-- Stage 13.5 now has a closed density-uniform starting modulus. -/
theorem lemma_13_5_uniform_density_explicit {delta : Real} (hδ : 0 < delta)
    (N : Nat) [Fact N.Prime] (S : Section13Context N) (D : Stage134Data N)
    (hS : delta ≤ S.alpha) (hN : section13DensityRecurrenceThreshold delta ≤ N)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  have hs := section13_uniform_density_recurrence_scale_explicit hδ N hN S.alpha hS D.q D.m D.P.length
    h134.1 h134.2.2.2.2.1 h134.2.2.2.2.2.1 h134.2.2.2.2.2.2.1
  have hNthree : 3 ≤ N := (le_max_left _ _).trans hN
  exact lemma_13_5_with_scale (Fact.out : N.Prime) (bne_iff_ne.mpr (by omega))
    S D (section10Lambda (S.alpha ^ 32 / 16)) h134 hs.1 hs.2.1 hs.2.2

/-- Stage 13.5 constructed with a threshold depending only on a positive
lower bound for the context density. -/
theorem lemma_13_5_uniform_density {delta : Real} (hδ : 0 < delta) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime] (S : Section13Context N) (D : Stage134Data N),
      delta ≤ S.alpha → N₀ ≤ N →
      IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D →
      ∃ E : Stage135Data N, IsStage135Data S D E := by
  refine ⟨section13DensityRecurrenceThreshold delta, ?_⟩
  intro N _ S D hS hN h134
  exact lemma_13_5_uniform_density_explicit hδ N S D hS hN h134

end

end LeanProofs.GowersSzemeredi
