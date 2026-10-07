import GowersSzemeredi.Proofs13UntrimmedRecurrence
import GowersSzemeredi.Proofs13LargeScaleRecurrence

/-! Removing endpoint deletion makes the ambient-modulus threshold depend
only on the Fourier cutoff, uniformly over every positive context density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem lemma_13_5_large_N_density_independent {theta : Real} (hθ : 0 < theta) :
    ∃ N₀ : Nat, ∀ (N : Nat) [Fact N.Prime]
      (S : Section13Context N) (D : Stage134Data N),
      N₀ ≤ N → IsStage134Data S theta D →
      ∃ E : Stage135Data N, IsStage135Data S D E ∧
        S.alpha ^ 32 * E.Q.length / 16 ≤ (criticalHeights S D E).card := by
  obtain ⟨N₀, hN₀⟩ := section13_uniform_recurrence_scale (alpha := 1) (by norm_num) hθ
  refine ⟨max N₀ 3, fun N _ S D hN h134 => ?_⟩
  have hscale := hN₀ N ((le_max_left _ _).trans hN) D.q D.m D.P.length
    h134.1 h134.2.2.2.2.1 h134.2.2.2.2.2.1 h134.2.2.2.2.2.2.1
  have hNthree : 3 ≤ N := (le_max_right _ _).trans hN
  exact lemma_13_5_without_endpoint_budget (Fact.out : N.Prime) (bne_iff_ne.mpr (by omega))
    S D theta h134 hscale.1 ((by norm_num : (4 : Real) ≤ 8).trans hscale.2.1)

end LeanProofs.GowersSzemeredi
