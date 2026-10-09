import GowersSzemeredi.Proofs16VarietyPieceClass

/-! A bounded family of variety pieces on each slice supplies the general
slice provider on every translated common-base good domain. The controls
depend on the total number of sampled pieces, with no cubic-class premise.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Final-coordinate slices covered by `Q` variety pieces yield the
polynomial provider on every common-base good domain. -/
theorem exists_variety_family_good_domain_slice_provider :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N D Q : Nat) [NeZero N] [Fact N.Prime] (c : Real),
    0 < Q → 0 < c → c ≤ 1 →
    ∀ (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N),
    Section16FinalStackable Q (section16VarietyPieceClass N D c) B phi →
    ∀ (H : Finset (Point N 2)) (Y : (a : Point N 2) → Finset (Section16CubeElement B a))
      (x0 : Point N 2),
    Section16SliceProvider (section16GoodDomain B H Y x0) (section16PhiOne phi x0)
      (fun r _ => 9 * (r * Q : Nat))
      (fun r _ => section16PolynomialJointVarietyExponent C p (r * Q) D c) ∧
    Section16SliceProviderRanges
      (fun r _ => 9 * (r * Q : Nat))
      (fun r _ => section16PolynomialJointVarietyExponent C p (r * Q) D c) := by
  classical
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_variety_piece_class_cover
  refine ⟨C, p, hC, hp, ?_⟩
  intro N D Q _ _ c hQ hc hc1 B phi hB H Y x0
  constructor
  · intro r sample
    choose E hE hcov using hB
    let e : Fin r × Fin Q ≃ Fin (r * Q) := finProdFinEquiv
    let F : Fin (r * Q) → Finset (Point N 2) × (Point N 2 → ZMod N) :=
      fun j => E (sample (e.symm j).1) (e.symm j).2
    let Gamma := section16FinsetUnion (fun j => partialGraph (F j).1 (F j).2)
    have hML := hcover N (r * Q) D c hc hc1 F (fun j => hE _ _) Gamma (fun _ hz => hz)
    apply (hML.translate (-x0)).subset
    intro z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
    have hz' := section16_goodDomain_slice_graph_subset B phi H Y x0 (sample i) hi
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz'
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (hcov (sample i) hw)
    refine Finset.mem_image.mpr ⟨w, Finset.mem_biUnion.mpr
      ⟨e (i, j), Finset.mem_univ _, ?_⟩, rfl⟩
    simpa only [F, Equiv.symm_apply_apply] using hj
  · intro r eps hr _ _
    have hrQ : 0 < r * Q := Nat.mul_pos hr hQ
    have hrQR : (1 : Real) ≤ (r * Q : Nat) := by exact_mod_cast hrQ
    exact ⟨by nlinarith, section16PolynomialJointVarietyExponent_pos C (r * Q) D hp hc hc1,
      section16PolynomialJointVarietyExponent_le_one hC hp (r * Q) D hc hc1⟩

end LeanProofs.GowersSzemeredi
