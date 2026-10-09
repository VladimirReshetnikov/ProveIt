import GowersSzemeredi.Proofs16DeepBoundDomination
import GowersSzemeredi.Proofs16VarietyStructureSlices

/-! The padded slice-class cover from the prime, eventual, any-bound contract.

`variety_structure_class_cover` (`Proofs16VarietyStructureSlices`) takes
`MilicevicDeepVarietyStructure D`. Here the input is
`MilicevicDeepEventuallyPrime Bnd` for an arbitrary bound function. The
exponent `D` is chosen from `(γ, θ)` by `exists_milicevicBound_ge` at the
extraction density, and the pieces are converted by `IsVarietyPieceB.toD`.
The conclusion has the same form, with `D` depending on `(γ, θ)`.

This module imports the OAI port through `Proofs16VarietyStructureSlices`, so
it is checked on the full-verification host. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **The padded slice-class cover from the prime, eventual contract.** -/
theorem variety_structure_class_cover_of_eventually {Bnd : Real → Real}
    (hM : MilicevicDeepEventuallyPrime Bnd)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ D : Nat, ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
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
  obtain ⟨hc, hc1⟩ := section16VarietyExtractionDensity_pos_le_one gamma ht ht1
  obtain ⟨D, hD⟩ := exists_milicevicBound_ge hc hc1
    (Bnd (section16VarietyExtractionDensity gamma theta))
  obtain ⟨N0, hcover⟩ := structure_side_of_milicevic_sharper_eventually hM gamma theta hg hg1 ht ht1
  have hbase := two_le_milicevic_base hc hc1
  have hB : 0 ≤ milicevicBound D (section16VarietyExtractionDensity gamma theta) :=
    pow_nonneg (by linarith) D
  refine ⟨D, N0, ?_⟩
  intro N _ _ hN Gamma hsize hprod
  obtain ⟨J, hJ, K, G, f, hK, hpiece, hcov⟩ := hcover N hN Gamma hsize hprod
  have hKQ : K ≤ section16VarietyExtractionCount D gamma theta := by
    have hexp : Real.exp (Bnd (section16VarietyExtractionDensity gamma theta)) ≤
        Real.exp (milicevicBound D (section16VarietyExtractionDensity gamma theta)) :=
      Real.exp_le_exp.mpr hD
    have hK' : (K : Real) ≤ (section16VarietyExtractionFamily gamma theta : Real) *
        Real.exp (milicevicBound D (section16VarietyExtractionDensity gamma theta)) :=
      hK.trans (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _))
    have hceil := hK'.trans (Nat.le_ceil _)
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
    · have hp : IsVarietyPiece D (section16VarietyExtractionDensity gamma theta)
          (f ⟨i, hi⟩) (G ⟨i, hi⟩) :=
        IsVarietyPieceB.toD hD (by
          simpa only [section16VarietyExtractionDensity, section16VarietyExtractionFamily]
            using hpiece ⟨i, hi⟩)
      simpa only [E, dif_pos hi] using hp.mem_section16VarietyPieceClass
    · simpa only [E, dif_neg hi] using
        empty_mem_section16VarietyPieceClass (N := N) D
          (section16VarietyExtractionDensity gamma theta) hB
  · intro z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (hcov hz)
    let j : Fin (section16VarietyExtractionCount D gamma theta) :=
      ⟨i, lt_of_lt_of_le i.isLt hKQ⟩
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
    simpa only [E, j, dif_pos i.isLt] using hi

end LeanProofs.GowersSzemeredi
