import GowersSzemeredi.Proofs16VarietyStructureSlices
import GowersSzemeredi.Proofs16VarietyFamilySlices

/-! The deep structure input yields the actual polynomial slice provider
after one controlled restriction, uniformly on all common-base good domains.
No separate assumption of structured slices or a cubic-stackable class remains.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The complete restriction-to-provider reduction from deep variety
structure. Every common-base good domain on the restricted set inherits
controls in the total number of sampled variety pieces. -/
theorem exists_restricted_variety_slice_provider :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ D : Nat, MilicevicDeepVarietyStructure D →
    ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N),
        HasProductProperty B phi gamma →
        ∃ A : Finset (Point N 3), A ⊆ B ∧
          (B.card : Real) - theta * (N : Real)^3 ≤ A.card ∧
          ∀ (H : Finset (Point N 2))
            (Y : (a : Point N 2) → Finset (Section16CubeElement A a)) (x0 : Point N 2),
          let Q := section16VarietyExtractionCount D gamma theta
          let c := section16VarietyExtractionDensity gamma theta
          Section16SliceProvider (section16GoodDomain A H Y x0) (section16PhiOne phi x0)
            (fun r _ => 9 * (r * Q : Nat))
            (fun r _ => section16PolynomialJointVarietyExponent C p (r * Q) D c) ∧
          Section16SliceProviderRanges
            (fun r _ => 9 * (r * Q : Nat))
            (fun r _ => section16PolynomialJointVarietyExponent C p (r * Q) D c) := by
  obtain ⟨C, p, hC, hp, hprovider⟩ := exists_variety_family_good_domain_slice_provider
  refine ⟨C, p, hC, hp, ?_⟩
  intro D hD gamma theta hg hg1 ht ht1
  obtain ⟨N0, hrestrict⟩ := restrict_final_variety_families hD gamma theta hg hg1 ht ht1
  obtain ⟨hc, hc1⟩ := section16VarietyExtractionDensity_pos_le_one gamma ht ht1
  have hQ : 0 < section16VarietyExtractionCount D gamma theta := Nat.succ_pos _
  refine ⟨N0, ?_⟩
  intro N _ _ hN B phi hprod
  obtain ⟨A, hAB, hmass, hA⟩ := hrestrict N hN B phi hprod
  exact ⟨A, hAB, hmass, fun H Y x0 =>
    hprovider N D _ _ hQ hc hc1 A phi hA H Y x0⟩

end LeanProofs.GowersSzemeredi
