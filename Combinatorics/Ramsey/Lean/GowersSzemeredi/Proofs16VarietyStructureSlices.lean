import GowersSzemeredi.Proofs16VarietyPieceClass
import GowersSzemeredi.Proofs16SharperVarietyStructure

/-! Uniform variety families on every final-coordinate slice, conditional
only on the deep variety structure theorem. Padding fixes the piece count
across slices; restricting all slices loses at most the prescribed mass.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16VarietyExtractionFamily (gamma theta : Real) : Nat :=
  bihomFamilySize (densePieceMassGen section16SharperLineMass) gamma (theta / 2)

def section16VarietyExtractionDensity (gamma theta : Real) : Real :=
  theta / 2 / section16VarietyExtractionFamily gamma theta

def section16VarietyExtractionCount (D : Nat) (gamma theta : Real) : Nat :=
  Nat.ceil ((section16VarietyExtractionFamily gamma theta : Real) *
    Real.exp (milicevicBound D (section16VarietyExtractionDensity gamma theta))) + 1

theorem section16VarietyExtractionDensity_pos_le_one (gamma : Real) {theta : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    0 < section16VarietyExtractionDensity gamma theta ∧
      section16VarietyExtractionDensity gamma theta ≤ 1 := by
  have hm : 1 ≤ section16VarietyExtractionFamily gamma theta := by
    unfold section16VarietyExtractionFamily bihomFamilySize
    omega
  have hmR : (1 : Real) ≤ section16VarietyExtractionFamily gamma theta := by exact_mod_cast hm
  unfold section16VarietyExtractionDensity
  constructor
  · exact div_pos (by positivity) (by linarith)
  · apply (div_le_one (by linarith)).mpr
    linarith

/-- Pad the extracted relation cover to a uniform count of class members. -/
theorem variety_structure_class_cover {D : Nat} (hM : MilicevicDeepVarietyStructure D)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
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
              section16FinsetUnion (fun i => partialGraph (E i).1 (E i).2) := by
  classical
  obtain ⟨N0, hcover⟩ := structure_side_of_milicevic_sharper hM gamma theta hg hg1 ht ht1
  obtain ⟨hc, hc1⟩ := section16VarietyExtractionDensity_pos_le_one gamma ht ht1
  have hbase := two_le_milicevic_base hc hc1
  have hB : 0 ≤ milicevicBound D (section16VarietyExtractionDensity gamma theta) :=
    pow_nonneg (by linarith) D
  refine ⟨N0, ?_⟩
  intro N _ _ hN Gamma hsize hprod
  obtain ⟨J, hJ, K, G, f, hK, hpiece, hcov⟩ := hcover N hN Gamma hsize hprod
  have hKQ : K ≤ section16VarietyExtractionCount D gamma theta := by
    have hceil := hK.trans (Nat.le_ceil _)
    have hnat : K ≤ Nat.ceil ((section16VarietyExtractionFamily gamma theta : Real) *
        Real.exp (milicevicBound D (section16VarietyExtractionDensity gamma theta))) := by
      exact_mod_cast hceil
    exact hnat.trans (Nat.le_succ _)
  let E : Fin (section16VarietyExtractionCount D gamma theta) →
      Finset (Point N 2) × (Point N 2 → ZMod N) := fun i =>
    if hi : (i : Nat) < K then
      ((G ⟨i, hi⟩).image pairPoint, fun x => f ⟨i, hi⟩ (x 0, x 1))
    else (∅, fun _ => 0)
  refine ⟨J, hJ, E, ?_, ?_⟩
  · intro i
    by_cases hi : (i : Nat) < K
    · simpa only [E, dif_pos hi, section16VarietyExtractionDensity,
        section16VarietyExtractionFamily] using (hpiece ⟨i, hi⟩).mem_section16VarietyPieceClass
    · simpa only [E, dif_neg hi] using
        empty_mem_section16VarietyPieceClass (N := N) D
          (section16VarietyExtractionDensity gamma theta) hB
  · intro z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (hcov hz)
    let j : Fin (section16VarietyExtractionCount D gamma theta) :=
      ⟨i, lt_of_lt_of_le i.isLt hKQ⟩
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
    simpa only [E, j, dif_pos i.isLt] using hi

/-- Restrict all slices to uniform variety families, losing at most
`theta*N^3` points. Deep variety structure remains the sole external input. -/
theorem restrict_final_variety_families {D : Nat} (hM : MilicevicDeepVarietyStructure D)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N 3)) (phi : Point N 3 → ZMod N),
        HasProductProperty B phi gamma →
        ∃ A : Finset (Point N 3), A ⊆ B ∧
          (B.card : Real) - theta * (N : Real)^3 ≤ A.card ∧
          Section16FinalStackable (section16VarietyExtractionCount D gamma theta)
            (section16VarietyPieceClass N D (section16VarietyExtractionDensity gamma theta))
            A phi := by
  obtain ⟨N0, hcover⟩ := variety_structure_class_cover hM gamma theta hg hg1 ht ht1
  exact ⟨N0, fun N _ _ hN B phi hprod =>
    section16_restrict_final_stackable hg hg1 _ (hcover N hN) B phi hprod⟩

end LeanProofs.GowersSzemeredi
