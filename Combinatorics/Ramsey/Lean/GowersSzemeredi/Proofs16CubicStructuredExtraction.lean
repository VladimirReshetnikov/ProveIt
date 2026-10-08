import GowersSzemeredi.Proofs16BaseCaseEndpoint
import GowersSzemeredi.Proofs16FreimanSliceExtraction
import GowersSzemeredi.Proofs16StructuredExtraction

/-! Strengthen dimension-two structured extraction by retaining fixed Freiman
families on its final-coordinate sections. All restrictions preserve these
witnesses. The extra preliminary restriction spends a quarter of the initial
density, leaving enough mass for the existing structured extraction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A dense product-property graph contains a structured pair with fixed
Freiman families on every final-coordinate section. -/
theorem section16_cubic_structured_extraction {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N → Odd N →
      ∀ (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N),
        theta * (N : Real)^2 ≤ B.card → HasProductProperty B phi gamma →
        ∃ C : Finset (Point N 2), C ⊆ B ∧
          Section16StructuredPair (theta / 2) gamma C phi ∧
          Section16FinalFreimanFamilies (section16BaseFamilyBound gamma (theta / 4)) C phi := by
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  have ht4 : 0 < theta / 4 := by positivity
  have ht41 : theta / 4 ≤ 1 := by linarith
  obtain ⟨Np, hNp⟩ := restrict_proper_faces_common_parameter 1
    (fun l hl hl1 => by
      have heq : l = 1 := by omega
      subst l
      exact lemma_16_3_holds)
    gamma (theta / 2) hg hg1 ht2 ht21
  obtain ⟨Na, hNa⟩ := lemma_15_6_of_density_lower_all 1 (theta / 4) gamma ht4 ht41 hg hg1
  refine ⟨max Np Na, ?_⟩
  intro N _ _ hN ho B phi hB hprod
  obtain ⟨B0, hB0, hB0mass, hfamily⟩ :=
    section16_restrict_final_freiman_families hg hg1 ht4 ht41 B phi hprod
  have hB0dense : theta / 2 * (N : Real)^2 ≤ B0.card := by
    have hv : 0 ≤ theta * (N : Real)^2 := by positivity
    nlinarith only [hB, hB0mass, hv]
  obtain ⟨B1, hB1, hB1mass, hfaces⟩ := hNp N ((le_max_left _ _).trans hN)
    B0 phi hB0dense (hprod.mono hB0)
  have hB1dense : theta / 4 * (N : Real)^2 ≤ B1.card := by
    convert hB1mass using 1
    ring
  obtain ⟨C, hC, hcount, hrespect⟩ := hNa N ((le_max_right _ _).trans hN)
    (Fact.out : N.Prime) ho B1 phi hB1dense (hprod.mono (hB1.trans hB0))
  refine ⟨C, hC.trans (hB1.trans hB0), ⟨hfaces.mono hC, ?_, ?_⟩,
    hfamily.mono (hC.trans hB1)⟩
  · have heq : theta / 4 * gamma / 2 = theta / 2 * gamma / 4 := by ring
    simpa only [section16ThetaOne, heq] using hcount
  · simpa only [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), Real.rpow_ofNat,
      inv_pow] using hrespect

end LeanProofs.GowersSzemeredi
