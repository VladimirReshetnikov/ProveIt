import GowersSzemeredi.Proofs16VarietyStructureSlices
import GowersSzemeredi.Proofs16PartJPiece

/-! Dimension-three structured extraction preserving the variety-family
slice property. The face and cube-respecting restrictions use the already
proved lower-dimensional structure results. Deep variety structure is the
only additional structural hypothesis.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Dimension-three structured extraction retaining stackable slices. -/
theorem variety_structured_extraction {D : Nat} (hD : MilicevicDeepVarietyStructure D)
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N → Odd N →
      ∀ (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N),
          theta * (N : Real) ^ 3 ≤ B.card → HasProductProperty B phi gamma →
          ∃ C : Finset (Point N 3), C ⊆ B ∧
            Section16StructuredPair (theta / 2) gamma C phi ∧
            Section16FinalStackable (section16VarietyExtractionCount D gamma (theta / 4))
              (section16VarietyPieceClass N D (section16VarietyExtractionDensity gamma (theta / 4))) C phi := by
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  have ht4 : 0 < theta / 4 := by positivity
  have ht41 : theta / 4 ≤ 1 := by linarith
  obtain ⟨Ns, hNs⟩ := restrict_final_variety_families hD gamma (theta / 4) hg hg1 ht4 ht41
  obtain ⟨Np, hNp⟩ := restrict_proper_faces_common_parameter 2
    (fun l hl hl2 => by
      rcases (by omega : l = 1 ∨ l = 2) with rfl | rfl
      · exact lemma_16_3_holds
      · exact theorem_16_2_at_two)
    gamma (theta / 2) hg hg1 ht2 ht21
  obtain ⟨Na, hNa⟩ := lemma_15_6_of_density_lower_all 2 (theta / 4) gamma ht4 ht41 hg hg1
  refine ⟨max Ns (max Np Na), fun N _ _ hN ho => ?_⟩
  intro B phi hB hprod
  obtain ⟨B0, hB0, hB0mass, hstack⟩ :=
    hNs N ((le_max_left _ _).trans hN) B phi hprod
  have hB0dense : theta / 2 * (N : Real) ^ 3 ≤ B0.card := by
    have hv : 0 ≤ theta * (N : Real) ^ 3 := by positivity
    nlinarith only [hB, hB0mass, hv]
  obtain ⟨B1, hB1, hB1mass, hfaces⟩ := hNp N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
    B0 phi hB0dense (hprod.mono hB0)
  have hB1dense : theta / 4 * (N : Real) ^ 3 ≤ B1.card := by
    convert hB1mass using 1
    ring
  obtain ⟨C, hC, hcount, hrespect⟩ := hNa N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
    (Fact.out : N.Prime) ho B1 phi hB1dense (hprod.mono (hB1.trans hB0))
  refine ⟨C, hC.trans (hB1.trans hB0), ⟨hfaces.mono hC, ?_, ?_⟩, hstack.mono (hC.trans hB1)⟩
  · have heq : theta / 4 * gamma / 2 = theta / 2 * gamma / 4 := by ring
    simpa only [section16ThetaOne, heq] using hcount
  · simpa only [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), Real.rpow_ofNat,
      inv_pow] using hrespect

end LeanProofs.GowersSzemeredi
