import GowersSzemeredi.Proofs16PowerCoverProfile
import GowersSzemeredi.Proofs16StructuredExtraction

/-! Construct large power-covered pieces from the preceding dimensions of
the structural theorem. The former separate contextual-lifting assumption
is unnecessary for this explicitly weaker, quantitatively proved profile. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Every relation with the product property and a large projection has a
uniformly large power-covered subrelation. Only preceding structural
dimensions are assumed; the all-ones lift and its mass transport are proved. -/
theorem section16_large_power_piece_of_dimension_induction {k : Nat} (hk : 1 ≤ k)
    (hth : ∀ l : Nat, 1 ≤ l → l ≤ k → Theorem162At l)
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N (k + 1) × ZMod N), RelationProductProperty gamma Gamma →
        theta * (N : Real) ^ (k + 1) ≤ (relationProjection Gamma).card →
        ∃ E ⊆ Gamma, (N : Real) ^ (k + 1) / multipleS theta gamma (k + 1) ≤ E.card ∧
          Section16PowerCoverProfile theta gamma k E := by
  obtain ⟨Ns, hNs⟩ := lemma_16_4_extraction k theta gamma ht ht1 hg hg1 hth
  obtain ⟨Nc, hNc⟩ := (hth k hk le_rfl).common_base_data theta gamma ht ht1 hg hg1
  refine ⟨max 3 (max Ns Nc), fun N _ _ hN Gamma hprod hlarge => ?_⟩
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNs' : Ns ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNc' : Nc ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have ho : Odd N := (Fact.out : N.Prime).odd_of_ne_two (by omega)
  rcases hNs N hNs' ho Gamma hprod with hsmall | ⟨B, phi, hgraph, hstructured⟩
  · obtain ⟨H, hH, hsupp⟩ := hsmall
    have hsub : relationProjection Gamma ⊆ H := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact hsupp z hz
    have hp : ((relationProjection Gamma).card : Real) ≤ H.card :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    linarith only [hlarge, hH, hp]
  · obtain ⟨D⟩ := hNc N hNc' B phi hstructured
    exact D.large_power_piece hstructured hk ht ht1 hg hg1 Gamma hgraph

end LeanProofs.GowersSzemeredi
