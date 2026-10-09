import GowersSzemeredi.Proofs16VarietyBudgetedPiece

/-! Relation pieces from local cover inputs, with separate family and spectrum indices.

The relation-piece layers of the variety route use the deep structure only
through `variety_structure_class_cover`, at two parameter pairs determined by
`(θ, γ)`:
* `(γ, θ/4)`, for the structured extraction (family index `D`);
* `(δ(θ₁), θ₁/8)` with `θ₁ = θ₁(θ/2, γ, 2)`, for the spectrum restriction
  (spectrum index `D₂`).

This module states those layers with the two covers as hypotheses
(`VarietyClassCoverAt`). So any form of the deep structure that supplies
the two covers suffices, in particular the eventual, polynomial-bound one,
where `D` and `D₂` are chosen per density. The proofs are those of the
`…At_of` layers with the cover inputs substituted:
* `variety_spectrum_restriction_local`,
  `variety_structured_extraction_local`;
* `polynomial_variety_structured_piece_local`,
  `polynomial_variety_product_graph_piece_local`,
  `polynomial_variety_relation_piece_local`;
* `section16_budgeted_piece_three_of_local`: `Section16BudgetedPieceAt 3`
  from, for each `(γ, θ)`, the two covers and the two Milićević values
  below `x^(2·2^256)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The padded slice-class cover at one parameter pair: the conclusion of
`variety_structure_class_cover`. -/
def VarietyClassCoverAt (D : Nat) (gamma theta : Real) : Prop :=
  ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
    ∀ Gamma : Finset (Point N 2 × ZMod N),
      (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real)^2 →
      RelationProductProperty gamma Gamma →
      ∃ J : Finset (Point N 2), (1 - theta) * (N : Real)^2 ≤ J.card ∧
        ∃ E : Fin (section16VarietyExtractionCount D gamma theta) →
          Finset (Point N 2) × (Point N 2 → ZMod N),
          (∀ i, E i ∈ section16VarietyPieceClass N D
            (section16VarietyExtractionDensity gamma theta)) ∧
          restrictRelation Gamma J ⊆
            section16FinsetUnion (fun i => partialGraph (E i).1 (E i).2)

/-- Deep variety structure supplies the cover at every pair. -/
theorem MilicevicDeepVarietyStructure.varietyClassCoverAt {D : Nat}
    (hM : MilicevicDeepVarietyStructure D) {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) : VarietyClassCoverAt D gamma theta :=
  variety_structure_class_cover hM gamma theta hg hg1 ht ht1

/-- **The spectrum restriction from a local cover.** -/
theorem variety_spectrum_restriction_local {C p : Nat} (hcover : VarietyPieceClassCoverAt C p)
    {D : Nat} {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1)
    (hcovS : VarietyClassCoverAt D (section16Delta (section16ThetaOne theta gamma 2))
      (section16ThetaOne theta gamma 2 / 8)) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ B : Finset (Point N 3), ∃ J : Finset (Point N 2),
        (1 - section16ThetaOne theta gamma 2 / 8) * (N : Real)^2 ≤ J.card ∧
        MultiplyLinearWith (fun _ => 9 * section16VarietySpectrumCount D theta gamma)
          (fun _ => section16PolynomialJointVarietyExponent C p
            (section16VarietySpectrumCount D theta gamma) D
            (section16VarietySpectrumDensity theta gamma))
          (restrictRelation (section16SpectrumRelation B
            (section16Delta (section16ThetaOne theta gamma 2))) J) := by
  obtain ⟨ha, ha1, hd, hd1⟩ := section16_theta_delta_bounds 2 ht ht1 hg hg1
  obtain ⟨hc, hc1⟩ := section16VarietySpectrumDensity_pos_le_one ht ht1 hg hg1
  obtain ⟨N0, hstructure⟩ := hcovS
  refine ⟨N0, ?_⟩
  intro N _ _ hN B
  obtain ⟨J, hJ, E, hE, hcov⟩ := hstructure N hN _
    (section16_spectrum_relation_card B hd) (section16_spectrum_relation_product B hd)
  exact ⟨J, hJ, hcover N _ D _ hc hc1 E hE _ hcov⟩

/-- **The structured extraction from a local cover at `(γ, θ/4)`.** -/
theorem variety_structured_extraction_local {D : Nat} {theta gamma : Real} (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hcovE : VarietyClassCoverAt D gamma (theta / 4)) :
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
  obtain ⟨Ns, hcov⟩ := hcovE
  have hNs := fun (N : Nat) [NeZero N] [Fact N.Prime] (hN : Ns ≤ N) (B : Finset (Point N 3))
      (phi : Point N 3 → ZMod N) (hprod : HasProductProperty B phi gamma) =>
    section16_restrict_final_stackable hg hg1 _ (hcov N hN) B phi hprod
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

/-- **Structured pieces from a local spectrum cover**, with family index `D`
and spectrum index `D₂`. -/
theorem polynomial_variety_structured_piece_local {C p Cv pv Cs ps : Nat} (hCs : 2 ≤ Cs)
    (hps : 0 < ps) (hcover : PolynomialVarietyCommonBaseCoverAt C p Cv pv)
    (hclass : VarietyPieceClassCoverAt Cs ps) {D₂ : Nat} {theta gamma : Real} (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hcovS : VarietyClassCoverAt D₂ (section16Delta (section16ThetaOne theta gamma 2))
      (section16ThetaOne theta gamma 2 / 8)) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (D Q : Nat) (c : Real), 0 < Q → 0 < c → c ≤ 1 →
      ∀ (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N),
        Section16StructuredPair theta gamma B phi →
        Section16FinalStackable Q (section16VarietyPieceClass N D c) B phi →
        ∃ Gamma : Finset (Point N 3 × ZMod N), Gamma ⊆ partialGraph B phi ∧
          section16ThetaTwo (section16ThetaOne theta gamma 2) * (N : Real)^3 ≤ Gamma.card ∧
          MultiplyLinearWith (fun rho => max (section16VarietyLiftGraphBound Q theta gamma rho) 27)
            (section16PolynomialVarietyThreeExponent2 C p Cv pv Cs ps D D₂ Q c theta gamma) Gamma := by
  obtain ⟨N0, hspec⟩ := variety_spectrum_restriction_local hclass ht ht1 hg hg1 hcovS
  obtain ⟨hcs, hcs1⟩ := section16VarietySpectrumDensity_pos_le_one ht ht1 hg hg1
  refine ⟨N0, ?_⟩
  intro N _ _ hN D Q c hQ hc hc1 B phi h hfamily
  obtain ⟨data⟩ := section16_common_base_data_with ht ht1 hg hg1 h (hspec N hN B)
  have hML := hcover N theta gamma ht ht1 hg hg1 _ _
    (fun s _ _ => ⟨by positivity,
      section16PolynomialJointVarietyExponent_pos Cs _ D₂ hps hcs hcs1,
      section16PolynomialJointVarietyExponent_le_one hCs hps _ D₂ hcs hcs1⟩)
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

/-- **Product graph pieces from the two local covers.** -/
theorem polynomial_variety_product_graph_piece_local {C p Cv pv Cs ps : Nat} (hCs : 2 ≤ Cs)
    (hps : 0 < ps) (hcover : PolynomialVarietyCommonBaseCoverAt C p Cv pv)
    (hclass : VarietyPieceClassCoverAt Cs ps) {D D₂ : Nat} {theta gamma : Real} (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hcovE : VarietyClassCoverAt D gamma (theta / 4))
    (hcovS : VarietyClassCoverAt D₂ (section16Delta (section16ThetaOne (theta / 2) gamma 2))
      (section16ThetaOne (theta / 2) gamma 2 / 8)) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N → Odd N →
      ∀ (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N),
        theta * (N : Real)^3 ≤ B.card → HasProductProperty B phi gamma →
        ∃ Gamma : Finset (Point N 3 × ZMod N), Gamma ⊆ partialGraph B phi ∧
          section16ThetaTwo (section16ThetaOne (theta / 2) gamma 2) * (N : Real)^3 ≤ Gamma.card ∧
          MultiplyLinearWith (section16VarietyThreeGraphBound D theta gamma)
            (section16VarietyThreePieceExponent2 C p Cv pv Cs ps D D₂ theta gamma) Gamma := by
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  obtain ⟨Ns, hs⟩ := variety_structured_extraction_local ht ht1 hg hg1 hcovE
  obtain ⟨Np, hp'⟩ := polynomial_variety_structured_piece_local hCs hps hcover hclass ht2 ht21
    hg hg1 hcovS
  obtain ⟨hc, hc1⟩ := section16VarietyExtractionDensity_pos_le_one gamma
    (by positivity : 0 < theta / 4) (by linarith)
  refine ⟨max Ns Np, ?_⟩
  intro N _ _ hN hodd B phi hB hprod
  obtain ⟨A, hAB, hA, hfamily⟩ := hs N ((le_max_left _ _).trans hN) hodd B phi hB hprod
  obtain ⟨Gamma, hGamma, hmass, hML⟩ := hp' N ((le_max_right _ _).trans hN) D _ _
    (Nat.succ_pos _) hc hc1 A phi hA hfamily
  exact ⟨Gamma, hGamma.trans (partialGraph_mono phi hAB), hmass, hML⟩

/-- **Relation pieces from the two local covers.** -/
theorem polynomial_variety_relation_piece_local {C p Cv pv Cs ps : Nat} (hCs : 2 ≤ Cs)
    (hps : 0 < ps) (hcover : PolynomialVarietyCommonBaseCoverAt C p Cv pv)
    (hclass : VarietyPieceClassCoverAt Cs ps) {D D₂ : Nat} {theta gamma : Real} (ht : 0 < theta)
    (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hcovE : VarietyClassCoverAt D gamma (theta / 4))
    (hcovS : VarietyClassCoverAt D₂ (section16Delta (section16ThetaOne (theta / 2) gamma 2))
      (section16ThetaOne (theta / 2) gamma 2 / 8)) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 3 × ZMod N),
        RelationProductProperty gamma Gamma →
        theta * (N : Real)^3 ≤ (relationProjection Gamma).card →
        ∃ Piece ⊆ Gamma, section16VarietyPieceMass theta gamma * (N : Real)^3 ≤ Piece.card ∧
          MultiplyLinearWith (section16VarietyThreeGraphBound D theta gamma)
            (section16VarietyThreePieceExponent2 C p Cv pv Cs ps D D₂ theta gamma) Piece := by
  obtain ⟨N0, hN0⟩ := polynomial_variety_product_graph_piece_local hCs hps hcover hclass
    ht ht1 hg hg1 hcovE hcovS
  refine ⟨max 3 N0, ?_⟩
  intro N _ _ hN Gamma hprod hlarge
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have ho : Odd N := (Fact.out : N.Prime).odd_of_ne_two (by omega)
  obtain ⟨phi, hgraph⟩ := relationProjection_graph_selection Gamma
  obtain ⟨Piece, hPiece, hmass, hML⟩ := hN0 N ((le_max_right _ _).trans hN) ho
    (relationProjection Gamma) phi hlarge (hprod _ phi hgraph)
  refine ⟨Piece, ?_, hmass, hML⟩
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hPiece hz)
  exact hgraph x hx

/-- The common-base cover at the named constants. -/
theorem polynomialVarietyCommonBaseCoverAt_explicit :
    PolynomialVarietyCommonBaseCoverAt explicitLiftK explicitLiftP
      explicitVarietyK explicitVarietyP := by
  have hC := two_le_explicitLiftK
  have hp := explicitLiftP_pos
  have hCv := two_le_explicitVarietyK
  have hpv := explicitVarietyP_pos
  exact polynomialVarietyCommonBaseCoverAt_of hC hp hCv hpv
    (polynomialVarietyFamilyPowerCoverAt_of hC hp hCv hpv
      allScalePolynomialMultilinearCoverAt_explicit
      (varietyFamilyGoodDomainSliceProviderAt_of hCv hpv varietyPieceClassCoverAt_explicit))

/-- **The source's piece budget in dimension three from local inputs.** For every
`(γ, θ)`, two indices with the two covers and the two Milićević values below
`x^(2·2^256)` suffice. -/
theorem section16_budgeted_piece_three_of_local
    (hconst : (explicitLiftK : Real) ≤ 2 ^ 1700 ∧ (explicitLiftP : Real) ≤ 2 ^ 1700 ∧
      (explicitVarietyK : Real) ≤ 2 ^ 1700 ∧ (explicitVarietyP : Real) ≤ 2 ^ 1700)
    (hinputs : ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      ∃ D D₂ : Nat, VarietyClassCoverAt D gamma (theta / 4) ∧
        VarietyClassCoverAt D₂ (section16Delta (section16ThetaOne (theta / 2) gamma 2))
          (section16ThetaOne (theta / 2) gamma 2 / 8) ∧
        milicevicBound D (section16VarietyExtractionDensity gamma (theta / 4)) ≤
          (2 / (theta * gamma)) ^ (2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) ∧
        milicevicBound D₂ (section16VarietySpectrumDensity (theta / 2) gamma) ≤
          (2 / (theta * gamma)) ^ (2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6)))) :
    Section16BudgetedPieceAt 3 := by
  intro gamma theta hg hg1 ht ht1
  obtain ⟨D, D₂, hcovE, hcovS, hm1, hm2⟩ := hinputs gamma theta hg hg1 ht ht1
  have hs1 : 1 ≤ section16VarietyThreeParameter D D₂ theta gamma := by
    clear hm1 hm2
    unfold section16VarietyThreeParameter
    have hL0 := section16VarietyThreeLoss_nonneg D D₂ theta gamma
    have hr := one_le_section16Lemma9R_half_two ht ht1 hg hg1
    have : 0 ≤ 18 * section16Lemma9R (theta / 2) gamma 2 / gamma :=
      div_nonneg (by linarith) hg.le
    linarith
  obtain ⟨hWpos, hL⟩ := section16VarietyThreeLoss_le_of_bounds ht ht1 hg hg1 hm1 hm2 hconst
  have hs := variety_piece_budget ht ht1 hg hg1 hL
  clear hL hm1 hm2
  refine ⟨section16VarietyPieceMass theta gamma, section16VarietyThreeParameter D D₂ theta gamma,
    section16VarietyPieceMass_pos ht hg, hs1, hs, ?_⟩
  obtain ⟨N0, hN0⟩ := polynomial_variety_relation_piece_local two_le_explicitVarietyK
    explicitVarietyP_pos polynomialVarietyCommonBaseCoverAt_explicit
    varietyPieceClassCoverAt_explicit ht ht1 hg hg1 hcovE hcovS
  refine ⟨N0, fun N _ _ hN Gamma _ hprod hlarge => ?_⟩
  obtain ⟨Piece, hPiece, hmass, hML⟩ := hN0 N hN Gamma hprod hlarge
  exact ⟨Piece, hPiece, hmass, hML.variety_three_multiplyLinear ht ht1 hg hg1 hWpos⟩

end LeanProofs.GowersSzemeredi
