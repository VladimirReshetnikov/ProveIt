import GowersSzemeredi.Proofs16ProgressionBridgeGeometry

/-! Nested shrinking keeps the bridge candidates away from the boundary:
sixteenth-progression endpoints have an eighth-progression supply of
bridges inside the quarter progression. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem centered_progression_shrink_comp {N : Nat} (Q : CenteredProgression N) (m n : Nat) :
    centeredProgressionShrink (centeredProgressionShrink Q m) n =
      centeredProgressionShrink Q (m*n) := by
  cases Q
  simp only [centeredProgressionShrink, centeredProgressionResize, Nat.div_div_eq_div_mul]

theorem centered_progression_sixteenth_subset_quarter {N : Nat} (Q : CenteredProgression N) :
    (centeredProgressionShrink Q 16).carrier ⊆ (centeredProgressionShrink Q 4).carrier := by
  simpa only [centered_progression_shrink_comp, Nat.reduceMul] using
    centered_progression_shrink_subset (centeredProgressionShrink Q 4) 4

theorem centered_progression_eighth_subset_quarter {N : Nat} (Q : CenteredProgression N) :
    (centeredProgressionShrink Q 8).carrier ⊆ (centeredProgressionShrink Q 4).carrier := by
  simpa only [centered_progression_shrink_comp, Nat.reduceMul] using
    centered_progression_shrink_subset (centeredProgressionShrink Q 4) 2

/-- Every eighth-progression candidate and its prescribed shift stay in
quarter progression. The endpoints need only lie in the sixteenth. -/
theorem centered_progression_second_bridge_mem {N : Nat} (Q : CenteredProgression N)
    {a c y : ZMod N} (ha : a ∈ (centeredProgressionShrink Q 16).carrier)
    (hc : c ∈ (centeredProgressionShrink Q 16).carrier)
    (hy : y ∈ (centeredProgressionShrink Q 8).carrier) :
    y ∈ (centeredProgressionShrink Q 4).carrier ∧
      y+(c-a) ∈ (centeredProgressionShrink Q 4).carrier := by
  have h := centered_progression_bridge_mem (centeredProgressionShrink Q 4)
    (by simpa only [centered_progression_shrink_comp, Nat.reduceMul] using hc)
    (by simpa only [centered_progression_shrink_comp, Nat.reduceMul] using ha)
    (by simpa only [centered_progression_shrink_comp, Nat.reduceMul] using hy)
  exact Finset.mem_filter.mp h

def progressionPurificationVertexThreshold {N : Nat} (Q : CenteredProgression N) : Nat :=
  (centeredProgressionShrink Q 8).carrier.card/8

theorem progression_vertex_threshold_reserve {N : Nat} (Q : CenteredProgression N) :
    4*progressionPurificationVertexThreshold Q < (centeredProgressionShrink Q 8).carrier.card := by
  have hzero : (0 : ZMod N) ∈ (centeredProgressionShrink Q 8).carrier :=
    (centered_progression_mem_iff _ 0).mpr ⟨fun _ => 0, by simp, by simp⟩
  have hpos := Finset.card_pos.mpr ⟨0,hzero⟩
  dsimp only [progressionPurificationVertexThreshold]
  omega

end LeanProofs.GowersSzemeredi
