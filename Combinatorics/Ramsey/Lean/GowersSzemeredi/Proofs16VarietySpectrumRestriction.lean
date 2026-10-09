import GowersSzemeredi.Proofs16VarietyStructureSlices
import GowersSzemeredi.Proofs16PartJPiece

/-! The two-dimensional spectrum relation receives the joint polynomial
variety cover after one base restriction. Its controls are independent of
the inner covering loss; deep variety structure remains the input.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16VarietySpectrumCount (D : Nat) (theta gamma : Real) : Nat :=
  section16VarietyExtractionCount D (section16Delta (section16ThetaOne theta gamma 2))
    (section16ThetaOne theta gamma 2 / 8)

def section16VarietySpectrumDensity (theta gamma : Real) : Real :=
  section16VarietyExtractionDensity (section16Delta (section16ThetaOne theta gamma 2))
    (section16ThetaOne theta gamma 2 / 8)

theorem section16VarietySpectrumCount_pos (D : Nat) (theta gamma : Real) :
    0 < section16VarietySpectrumCount D theta gamma := Nat.succ_pos _

theorem section16VarietySpectrumDensity_pos_le_one {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16VarietySpectrumDensity theta gamma ∧
      section16VarietySpectrumDensity theta gamma ≤ 1 := by
  obtain ⟨ha, ha1, -, -⟩ := section16_theta_delta_bounds 2 ht ht1 hg hg1
  exact section16VarietyExtractionDensity_pos_le_one _ (by positivity) (by linarith)

/-- The statement of `exists_variety_spectrum_restriction` at fixed constants. -/
def VarietySpectrumRestrictionAt (C p : Nat) : Prop :=
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
    ∀ theta gamma : Real, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ B : Finset (Point N 3), ∃ J : Finset (Point N 2),
        (1 - section16ThetaOne theta gamma 2 / 8) * (N : Real)^2 ≤ J.card ∧
        MultiplyLinearWith (fun _ => 9 * section16VarietySpectrumCount D theta gamma)
          (fun _ => section16PolynomialJointVarietyExponent C p
            (section16VarietySpectrumCount D theta gamma) D
            (section16VarietySpectrumDensity theta gamma))
          (restrictRelation (section16SpectrumRelation B
            (section16Delta (section16ThetaOne theta gamma 2))) J)

/-- `exists_variety_spectrum_restriction` at the constants of its input. -/
theorem varietySpectrumRestrictionAt_of {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hcover : VarietyPieceClassCoverAt C p) : VarietySpectrumRestrictionAt C p := by
  unfold VarietySpectrumRestrictionAt
  intro D hD theta gamma ht ht1 hg hg1
  obtain ⟨ha, ha1, hd, hd1⟩ := section16_theta_delta_bounds 2 ht ht1 hg hg1
  obtain ⟨hc, hc1⟩ := section16VarietySpectrumDensity_pos_le_one ht ht1 hg hg1
  obtain ⟨N0, hstructure⟩ := variety_structure_class_cover hD _ _ hd hd1
    (by positivity : 0 < section16ThetaOne theta gamma 2 / 8) (by linarith)
  refine ⟨N0, ?_⟩
  intro N _ _ hN B
  obtain ⟨J, hJ, E, hE, hcov⟩ := hstructure N hN _
    (section16_spectrum_relation_card B hd) (section16_spectrum_relation_product B hd)
  exact ⟨J, hJ, hcover N _ D _ hc hc1 E hE _ hcov⟩

/-- The spectrum cover has a constant graph count and width exponent as
the allowed covering loss varies. -/
theorem exists_variety_spectrum_restriction :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
    ∀ theta gamma : Real, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ B : Finset (Point N 3), ∃ J : Finset (Point N 2),
        (1 - section16ThetaOne theta gamma 2 / 8) * (N : Real)^2 ≤ J.card ∧
        MultiplyLinearWith (fun _ => 9 * section16VarietySpectrumCount D theta gamma)
          (fun _ => section16PolynomialJointVarietyExponent C p
            (section16VarietySpectrumCount D theta gamma) D
            (section16VarietySpectrumDensity theta gamma))
          (restrictRelation (section16SpectrumRelation B
            (section16Delta (section16ThetaOne theta gamma 2))) J) := by
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_variety_piece_class_cover
  exact ⟨C, p, hC, hp, varietySpectrumRestrictionAt_of hC hp hcover⟩

end LeanProofs.GowersSzemeredi
