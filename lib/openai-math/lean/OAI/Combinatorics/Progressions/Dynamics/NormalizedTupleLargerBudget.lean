import OAI.Combinatorics.Progressions.Estimates.AllocatedTupleSideThreshold

namespace OAI

section

namespace Erdos3

theorem normalizedTuple_log_mono (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G)
    {p E l P F L : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hpP : p ≤ P) (hEF : E ≤ F) (hlL : l ≤ L) :
    normalizedTupleWidthLog N s p E ≤ normalizedTupleWidthLog N s P F ∧
      normalizedTupleSideLog X N s p E l ≤ normalizedTupleSideLog X N s P F L := by
  have hP := hp.trans hpP
  have hF := hE.trans hEF
  have hL := hl.trans hlL
  constructor
  · dsimp only [normalizedTupleWidthLog, anisotropicTupleEarlyBudget, spatialTupleToleranceLog,
      spatialDisplacementLog, spatialProfileLog, anisotropicSpatialCapLog, coefficientErrorVolumeLog]
    gcongr
  · dsimp only [normalizedTupleSideLog, normalizedTupleLateBudget, normalizedTupleWidthLog,
      anisotropicTupleEarlyBudget, spatialTupleToleranceLog, spatialDiscretizationLog,
      anisotropicSpatialMeshLog, spatialDisplacementLog, spatialProfileLog,
      anisotropicSpatialCapLog, coefficientErrorVolumeLog]
    gcongr

theorem normalizedTuple_log_envelopes_of_le (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G)
    {p E l P : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) (hpP : p ≤ P)
    (hq : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ P)
    (hG : (Fintype.card G : ℝ) ≤ P) (hN : (Fintype.card N : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) :
    normalizedTupleWidthLog N s p E ≤ tupleWidthLogEnvelope P E ∧
      normalizedTupleSideLog X N s p E l ≤ tupleSideLogEnvelope P E l := by
  obtain ⟨hwidth, hside⟩ := normalizedTuple_log_mono X N s hp hE hl hpP le_rfl le_rfl
  obtain ⟨hwidth', hside'⟩ := normalizedTuple_log_envelopes X N s (hp.trans hpP) hE hl hq hG hN hX
  exact ⟨hwidth.trans hwidth', hside.trans hside'⟩

end Erdos3

end

end OAI
