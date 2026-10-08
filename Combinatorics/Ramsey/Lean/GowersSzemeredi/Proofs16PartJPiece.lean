import GowersSzemeredi.Proofs16PartJSlices
import GowersSzemeredi.Proofs16CubicRelationDecomposition
import GowersSzemeredi.Proofs16DimensionTwo

/-! Part J: dimension-three pieces from the stackable structure input.

This module assumes the dimension-two stackable structure
(`StackableStructureAt 2 Q q`) and repeats the dimension-two cubic
construction one dimension up. It proves:

* a dimension-two spectrum restriction whose graph count does not depend on
  the inner loss (`partJ_spectrum_restriction`);
* the dimension-three structured extraction, which keeps stackable slices
  (`partJ_structured_extraction`). Its face restrictions use the proved
  `Theorem162At 1` and `Theorem162At 2`;
* the cubic affine lift at `k = 2`, giving a dimension-three graph piece
  with explicit controls (`partJ_structured_piece`);
* the relation version with a positive mass fraction
  (`partJ_relation_piece`).

Comparing these controls with the source's `multipleQ` / `multipleC` in
dimension three is the remaining numerical step of Part J. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The spectrum graph count supplied by the stackable structure. -/
def partJSpectrumCount (Q q : Real → Real → Nat) (theta gamma : Real) : Nat :=
  Q (section16Delta (section16ThetaOne theta gamma 2)) (section16ThetaOne theta gamma 2 / 8) *
    q (section16Delta (section16ThetaOne theta gamma 2)) (section16ThetaOne theta gamma 2 / 8)

theorem partJSpectrumCount_pos {Q q : Real → Real → Nat} (hyp : StackableStructureAt 2 Q q)
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < partJSpectrumCount Q q theta gamma := by
  obtain ⟨ha, ha1, hd, hd1⟩ := section16_theta_delta_bounds 2 ht ht1 hg hg1
  obtain ⟨hQ, hq, -⟩ := hyp _ _ hd hd1
    (by positivity : 0 < section16ThetaOne theta gamma 2 / 8) (by linarith)
  exact Nat.mul_pos hQ hq

/-- The dimension-two spectrum relation of a dimension-three set admits a
restriction with loss-independent count and cubic exponent. -/
theorem partJ_spectrum_restriction {Q q : Real → Real → Nat} (hyp : StackableStructureAt 2 Q q)
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ B : Finset (Point N 3), ∃ J : Finset (Point N 2),
        (1 - section16ThetaOne theta gamma 2 / 8) * (N : Real) ^ 2 ≤ J.card ∧
        MultiplyLinearWith (fun _ => ((3 * partJSpectrumCount Q q theta gamma : Nat) : Real))
          (cubicBaseExponent (partJSpectrumCount Q q theta gamma))
          (restrictRelation (section16SpectrumRelation B
            (section16Delta (section16ThetaOne theta gamma 2))) J) := by
  obtain ⟨ha, ha1, hd, hd1⟩ := section16_theta_delta_bounds 2 ht ht1 hg hg1
  obtain ⟨hQ, -, N0, hN0⟩ := hyp _ _ hd hd1
    (by positivity : 0 < section16ThetaOne theta gamma 2 / 8) (by linarith)
  refine ⟨N0, fun N _ _ hN B => ?_⟩
  obtain ⟨S, hS, hcov⟩ := hN0 N hN
  obtain ⟨J, hJ, D, hD, hc⟩ := hcov _ (section16_spectrum_relation_card B hd)
    (section16_spectrum_relation_product B hd)
  exact ⟨J, hJ, hS _ hQ D hD _ hc⟩

/-- Dimension-three structured extraction retaining stackable slices. -/
theorem partJ_structured_extraction {Q q : Real → Real → Nat} (hyp : StackableStructureAt 2 Q q)
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N → Odd N →
      ∃ S : Set (Finset (Point N 2) × (Point N 2 → ZMod N)),
        CubicStackableClass 2 (q gamma (theta / 4)) S ∧
        ∀ (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N),
          theta * (N : Real) ^ 3 ≤ B.card → HasProductProperty B phi gamma →
          ∃ C : Finset (Point N 3), C ⊆ B ∧
            Section16StructuredPair (theta / 2) gamma C phi ∧
            Section16FinalStackable (Q gamma (theta / 4)) S C phi := by
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  have ht4 : 0 < theta / 4 := by positivity
  have ht41 : theta / 4 ≤ 1 := by linarith
  obtain ⟨-, -, Ns, hNs⟩ := hyp gamma (theta / 4) hg hg1 ht4 ht41
  obtain ⟨Np, hNp⟩ := restrict_proper_faces_common_parameter 2
    (fun l hl hl2 => by
      rcases (by omega : l = 1 ∨ l = 2) with rfl | rfl
      · exact lemma_16_3_holds
      · exact theorem_16_2_at_two)
    gamma (theta / 2) hg hg1 ht2 ht21
  obtain ⟨Na, hNa⟩ := lemma_15_6_of_density_lower_all 2 (theta / 4) gamma ht4 ht41 hg hg1
  refine ⟨max Ns (max Np Na), fun N _ _ hN ho => ?_⟩
  obtain ⟨S, hS, hcov⟩ := hNs N ((le_max_left _ _).trans hN)
  refine ⟨S, hS, fun B phi hB hprod => ?_⟩
  obtain ⟨B0, hB0, hB0mass, hstack⟩ :=
    section16_restrict_final_stackable (theta := theta / 4) hg hg1 S hcov B phi hprod
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

/-- The graph-count control of the dimension-three pieces. -/
def partJGraphBound (Q q : Real → Real → Nat) (theta gamma rho : Real) : Real :=
  max (section16CubicLiftGraphBound (Q gamma (theta / 4) * q gamma (theta / 4)) 2 (rho / 4)
    (theta / 2) gamma) 27

/-- The width-exponent control of the dimension-three pieces. -/
def partJExponent (Q q : Real → Real → Nat) (theta gamma rho : Real) : Real :=
  section16CappedWidthExponent
    (section16CubicLiftExponent (Q gamma (theta / 4) * q gamma (theta / 4)) 2 (rho / 4)
      (theta / 2) gamma
      (fun _ => ((3 * partJSpectrumCount Q q (theta / 2) gamma : Nat) : Real))
      (cubicBaseExponent (partJSpectrumCount Q q (theta / 2) gamma)))
    (section16CubicLiftThreshold (Q gamma (theta / 4) * q gamma (theta / 4)) 2 (rho / 4)
      (theta / 2) gamma
      (fun _ => ((3 * partJSpectrumCount Q q (theta / 2) gamma : Nat) : Real))
      (cubicBaseExponent (partJSpectrumCount Q q (theta / 2) gamma)))

/-- A structured pair with stackable slices and a stackable spectrum gives a
graph piece with the dimension-three cubic controls. -/
theorem partJ_structured_piece {N : Nat} [Fact N.Prime] {Q q : Real → Real → Nat}
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {S : Set (Finset (Point N 2) × (Point N 2 → ZMod N))}
    (hS : CubicStackableClass 2 (q gamma (theta / 4)) S)
    (hQ : 0 < Q gamma (theta / 4)) (hq : 0 < q gamma (theta / 4))
    (hn : 0 < partJSpectrumCount Q q (theta / 2) gamma)
    {C : Finset (Point N 3)} {phi : Point N 3 → ZMod N}
    (h : Section16StructuredPair (theta / 2) gamma C phi)
    (hstack : Section16FinalStackable (Q gamma (theta / 4)) S C phi)
    (hspec : ∃ J : Finset (Point N 2),
      (1 - section16ThetaOne (theta / 2) gamma 2 / 8) * (N : Real) ^ 2 ≤ J.card ∧
      MultiplyLinearWith (fun _ => ((3 * partJSpectrumCount Q q (theta / 2) gamma : Nat) : Real))
        (cubicBaseExponent (partJSpectrumCount Q q (theta / 2) gamma))
        (restrictRelation (section16SpectrumRelation C
          (section16Delta (section16ThetaOne (theta / 2) gamma 2))) J)) :
    ∃ Gamma : Finset (Point N 3 × ZMod N), Gamma ⊆ partialGraph C phi ∧
      section16ThetaTwo (section16ThetaOne (theta / 2) gamma 2) * (N : Real) ^ 3 ≤ Gamma.card ∧
      MultiplyLinearWith (partJGraphBound Q q theta gamma) (partJExponent Q q theta gamma) Gamma := by
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  obtain ⟨D⟩ := section16_common_base_data_with ht2 ht21 hg hg1 h hspec
  have hline := D.all_box_line_covers h
    (fun s hs hs1 => ⟨by positivity, cubicBaseExponent_pos hn hs, cubicBaseExponent_le_one hn hs hs1⟩)
    (by norm_num) ht2 ht21 hg hg1
  have hslice := hstack.good_domain_slice_provider hS hQ (D.H ∩ D.J) D.Y D.x0
  have hML := hline.cubic_multiplyLinearWith (Nat.mul_pos hQ hq) hslice (by norm_num) ht2 ht21
    hg hg1 (fun s hs _ => cubicBaseExponent_pos hn hs)
  refine ⟨section16TranslatedGoodGraph C phi (D.H ∩ D.J) D.Y D.x0, ?_, ?_, ?_⟩
  · apply section16TranslatedGoodGraph_subset
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · rw [section16TranslatedGoodGraph_card]
    exact D.good_mass
  · apply (hML.translate (appendCoordinate D.x0 0)).congr_controls
    · intro s _ _
      simp only [partJGraphBound]
      norm_num
    · intro s _ _
      rfl

/-- A large projection supplies a dimension-three piece of positive mass
with the cubic controls. -/
theorem partJ_relation_piece {Q q : Real → Real → Nat} (hyp : StackableStructureAt 2 Q q)
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ Gamma : Finset (Point N 3 × ZMod N),
        RelationProductProperty gamma Gamma →
        theta * (N : Real) ^ 3 ≤ (relationProjection Gamma).card →
        ∃ D ⊆ Gamma, section16ThetaTwo (section16ThetaOne (theta / 2) gamma 2) * (N : Real) ^ 3 ≤
            D.card ∧
          MultiplyLinearWith (partJGraphBound Q q theta gamma) (partJExponent Q q theta gamma) D := by
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  have ht4 : 0 < theta / 4 := by positivity
  have ht41 : theta / 4 ≤ 1 := by linarith
  obtain ⟨hQ, hq, -⟩ := hyp gamma (theta / 4) hg hg1 ht4 ht41
  have hn := partJSpectrumCount_pos hyp ht2 ht21 hg hg1
  obtain ⟨Ne, hNe⟩ := partJ_structured_extraction hyp ht ht1 hg hg1
  obtain ⟨Nsp, hNsp⟩ := partJ_spectrum_restriction hyp ht2 ht21 hg hg1
  refine ⟨max 3 (max Ne Nsp), fun N _ _ hN Gamma hprod hlarge => ?_⟩
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have ho : Odd N := (Fact.out : N.Prime).odd_of_ne_two (by omega)
  obtain ⟨S, hS, hext⟩ := hNe N ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) ho
  obtain ⟨phi, hgraph⟩ := relationProjection_graph_selection Gamma
  obtain ⟨C, hCB, hpair, hstack⟩ := hext (relationProjection Gamma) phi hlarge
    (hprod _ phi hgraph)
  obtain ⟨P, hP, hmass, hML⟩ := partJ_structured_piece ht ht1 hg hg1 hS hQ hq hn hpair hstack
    (hNsp N ((le_max_right _ _).trans ((le_max_right _ _).trans hN)) C)
  refine ⟨P, ?_, hmass, hML⟩
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hP hz)
  exact hgraph x (hCB hx)

end LeanProofs.GowersSzemeredi
