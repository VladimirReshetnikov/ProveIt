import GowersSzemeredi.Proofs16PolynomialVarietyCommonBaseCover
import GowersSzemeredi.Proofs16VarietySpectrumRestriction
import GowersSzemeredi.Proofs16VarietyStructuredExtraction

/-! Actual dimension-three graph pieces from deep variety structure.
The spectrum and slice covers are constructed with polynomial recurrence
controls. The remaining deep structure hypothesis is kept explicit.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16PolynomialVarietyThreeExponent (C p Cv pv Cs ps D Q : Nat)
    (c theta gamma rho : Real) : Real :=
  let Qb : Real → Real := fun _ => 9 * section16VarietySpectrumCount D theta gamma
  let Eb := fun _ : Real => section16PolynomialJointVarietyExponent Cs ps
    (section16VarietySpectrumCount D theta gamma) D (section16VarietySpectrumDensity theta gamma)
  section16CappedWidthExponent
    (section16PolynomialVarietyLiftExponent p Cv pv D Q c theta gamma Qb Eb rho)
    (section16PolynomialVarietyLiftThreshold C p Cv pv D Q c theta gamma Qb Eb rho)

/-- A structured three-dimensional pair with variety-family slices has
an actual dense graph piece. Its spectrum cover is constructed here. -/
theorem exists_polynomial_variety_structured_piece :
  ∃ C p Cv pv Cs ps : Nat, 2 ≤ C ∧ 0 < p ∧ 2 ≤ Cv ∧ 0 < pv ∧ 2 ≤ Cs ∧ 0 < ps ∧
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
    ∀ theta gamma : Real, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (Q : Nat) (c : Real), 0 < Q → 0 < c → c ≤ 1 →
      ∀ (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N),
        Section16StructuredPair theta gamma B phi →
        Section16FinalStackable Q (section16VarietyPieceClass N D c) B phi →
        ∃ Gamma : Finset (Point N 3 × ZMod N), Gamma ⊆ partialGraph B phi ∧
          section16ThetaTwo (section16ThetaOne theta gamma 2) * (N : Real)^3 ≤ Gamma.card ∧
          MultiplyLinearWith (fun rho => max (section16VarietyLiftGraphBound Q theta gamma rho) 27)
            (section16PolynomialVarietyThreeExponent C p Cv pv Cs ps D Q c theta gamma) Gamma := by
  obtain ⟨C, p, Cv, pv, hC, hp, hCv, hpv, hcover⟩ := exists_polynomial_variety_common_base_cover
  obtain ⟨Cs, ps, hCs, hps, hspectrum⟩ := exists_variety_spectrum_restriction
  refine ⟨C, p, Cv, pv, Cs, ps, hC, hp, hCv, hpv, hCs, hps, ?_⟩
  intro D hD theta gamma ht ht1 hg hg1
  obtain ⟨N0, hspec⟩ := hspectrum D hD theta gamma ht ht1 hg hg1
  obtain ⟨hcs, hcs1⟩ := section16VarietySpectrumDensity_pos_le_one ht ht1 hg hg1
  refine ⟨N0, ?_⟩
  intro N _ _ hN Q c hQ hc hc1 B phi h hfamily
  obtain ⟨data⟩ := section16_common_base_data_with ht ht1 hg hg1 h (hspec N hN B)
  have hML := hcover N theta gamma ht ht1 hg hg1 _ _
    (fun s _ _ => ⟨by positivity,
      section16PolynomialJointVarietyExponent_pos Cs _ D hps hcs hcs1,
      section16PolynomialJointVarietyExponent_le_one hCs hps _ D hcs hcs1⟩)
    B phi data h D Q c hQ hc hc1 hfamily
  refine ⟨section16TranslatedGoodGraph B phi (data.H ∩ data.J) data.Y data.x0, ?_, ?_, ?_⟩
  · apply section16TranslatedGoodGraph_subset
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · rw [section16TranslatedGoodGraph_card]
    exact data.good_mass
  · apply (hML.translate (appendCoordinate data.x0 0)).congr_controls
    · intro s _ _
      rfl
    · intro s _ _
      rfl

/-- Deep variety structure suffices to produce actual graph pieces from
the product property. No spectrum, slice, or selection premise remains. -/
theorem exists_polynomial_variety_product_graph_piece :
  ∃ C p Cv pv Cs ps : Nat, 2 ≤ C ∧ 0 < p ∧ 2 ≤ Cv ∧ 0 < pv ∧ 2 ≤ Cs ∧ 0 < ps ∧
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
    ∀ theta gamma : Real, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N → Odd N →
      ∀ (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N),
        theta * (N : Real)^3 ≤ B.card → HasProductProperty B phi gamma →
        ∃ Gamma : Finset (Point N 3 × ZMod N), Gamma ⊆ partialGraph B phi ∧
          section16ThetaTwo (section16ThetaOne (theta / 2) gamma 2) * (N : Real)^3 ≤ Gamma.card ∧
          MultiplyLinearWith
            (fun rho => max (section16VarietyLiftGraphBound
              (section16VarietyExtractionCount D gamma (theta / 4)) (theta / 2) gamma rho) 27)
            (section16PolynomialVarietyThreeExponent C p Cv pv Cs ps D
              (section16VarietyExtractionCount D gamma (theta / 4))
              (section16VarietyExtractionDensity gamma (theta / 4)) (theta / 2) gamma) Gamma := by
  obtain ⟨C, p, Cv, pv, Cs, ps, hC, hp, hCv, hpv, hCs, hps, hpiece⟩ :=
    exists_polynomial_variety_structured_piece
  refine ⟨C, p, Cv, pv, Cs, ps, hC, hp, hCv, hpv, hCs, hps, ?_⟩
  intro D hD theta gamma ht ht1 hg hg1
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  obtain ⟨Ns, hs⟩ := variety_structured_extraction hD ht ht1 hg hg1
  obtain ⟨Np, hp'⟩ := hpiece D hD (theta / 2) gamma ht2 ht21 hg hg1
  obtain ⟨hc, hc1⟩ := section16VarietyExtractionDensity_pos_le_one gamma
    (by positivity : 0 < theta / 4) (by linarith)
  refine ⟨max Ns Np, ?_⟩
  intro N _ _ hN hodd B phi hB hprod
  obtain ⟨A, hAB, hA, hfamily⟩ := hs N ((le_max_left _ _).trans hN) hodd B phi hB hprod
  obtain ⟨Gamma, hGamma, hmass, hML⟩ := hp' N ((le_max_right _ _).trans hN) _ _
    (Nat.succ_pos _) hc hc1 A phi hA hfamily
  exact ⟨Gamma, hGamma.trans (partialGraph_mono phi hAB), hmass, hML⟩

end LeanProofs.GowersSzemeredi
