import GowersSzemeredi.Proofs16LocalPairSelection
import GowersSzemeredi.Proofs16PrescribedDifferenceAnchors
import GowersSzemeredi.Proofs16MappedQuadrupleCount

/-! Actual local anchor families and source quadruples inside a proper progression.
All densities are explicit and relative to the retained progression mass. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The usual additive energy bound, in the native quadruple interface. -/
theorem additive_quadruples_density_lower {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) {delta : Real} (hd : 0 ≤ delta)
    (hS : delta*(N : Real) ≤ (S.card : Real)) :
    delta^4*(N : Real)^3 ≤ ((additiveQuadruplesIn S).card : Real) := by
  have heq : mappedAdditiveQuadruples S (id : ZMod N → ZMod N) = additiveQuadruplesIn S := by
    ext q
    simp only [mappedAdditiveQuadruples,additiveQuadruplesIn,Finset.mem_filter,
      Finset.mem_univ,true_and,Fintype.mem_piFinset,id_eq]
    exact and_comm
  have hnat := card_four_le_mapped_additive_quadruples S (id : ZMod N → ZMod N)
  rw [heq,ZMod.card] at hnat
  have hc : (S.card : Real)^4 ≤ (additiveQuadruplesIn S).card*(N : Real) := by exact_mod_cast hnat
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ delta*(N : Real)) hS 4
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply le_of_mul_le_mul_right _ hN
  calc (delta^4*(N : Real)^3)*N = (delta*(N : Real))^4 := by ring
    _ ≤ (S.card : Real)^4 := hp
    _ ≤ (additiveQuadruplesIn S).card*(N : Real) := hc

def localProgressionIndexDensity {N : Nat} (P : CenteredProgression N) (delta : Real) : Real :=
  delta/(2048 : Real)^P.rank

def localProgressionAnchorDensity {N : Nat} (P : CenteredProgression N) (delta : Real) : Real :=
  delta/(2*(1024 : Real)^P.rank)

/-- Shrinking the index progression supplies a positive uniform index density. -/
theorem local_progression_index_mass {N : Nat} [NeZero N]
    (P : CenteredProgression N) (hP : P.Proper) {delta : Real}
    (hmass : delta*(N : Real) ≤ (P.carrier.card : Real)) :
    localProgressionIndexDensity P delta*N ≤ ((centeredProgressionShrink P 1024).carrier.card : Real) := by
  have h := centered_progression_shrink_real_mass P hP (by norm_num : 0 < (1024 : Nat))
  norm_num only [Nat.cast_ofNat] at h
  have hmass' := (div_le_div_of_nonneg_right hmass (by positivity)).trans h
  simpa only [localProgressionIndexDensity,div_mul_eq_mul_div] using hmass'

/-- Every index in the shrinking has a linear-size family of valid local anchors. -/
theorem local_progression_anchor_mass {N : Nat} [NeZero N]
    (P : CenteredProgression N) (hP : P.Proper) {delta : Real} (hd : 0 < delta)
    (hmass : delta*(N : Real) ≤ (P.carrier.card : Real))
    {a : ZMod N} (ha : a ∈ (centeredProgressionShrink P 1024).carrier) :
    localProgressionAnchorDensity P delta*N ≤ ((progressionBridgeSet P.carrier a).card : Real) := by
  have hloss : (((centeredProgressionShrink P 256).carrier \ P.carrier).card : Real) ≤
      delta*N/(16*(1024 : Real)^P.rank) := by
    rw [Finset.sdiff_eq_empty_iff_subset.mpr (centered_progression_shrink_subset P 256),Finset.card_empty,Nat.cast_zero]
    positivity
  simpa only [localProgressionAnchorDensity,div_mul_eq_mul_div] using
    progression_difference_anchor_mass P hP P.carrier hd hmass hloss ha

/-- The same shrinking has a positive cubic-size original quadruple family. -/
theorem local_progression_quadruple_mass {N : Nat} [NeZero N]
    (P : CenteredProgression N) (hP : P.Proper) {delta : Real} (hd : 0 ≤ delta)
    (hmass : delta*(N : Real) ≤ (P.carrier.card : Real)) :
    (localProgressionIndexDensity P delta)^4*(N : Real)^3 ≤
      ((additiveQuadruplesIn (centeredProgressionShrink P 1024).carrier).card : Real) := by
  exact additive_quadruples_density_lower _ (by unfold localProgressionIndexDensity; positivity)
    (local_progression_index_mass P hP hmass)

theorem localProgressionAnchorDensity_pos {N : Nat} (P : CenteredProgression N)
    {delta : Real} (hd : 0 < delta) : 0 < localProgressionAnchorDensity P delta := by
  unfold localProgressionAnchorDensity
  positivity

theorem localProgressionIndexDensity_pos {N : Nat} (P : CenteredProgression N)
    {delta : Real} (hd : 0 < delta) : 0 < localProgressionIndexDensity P delta := by
  unfold localProgressionIndexDensity
  positivity

/-- The actual anchor lower bound is at most one, by testing the zero index. -/
theorem localProgressionAnchorDensity_le_one {N : Nat} [NeZero N]
    (P : CenteredProgression N) (hP : P.Proper) {delta : Real} (hd : 0 < delta)
    (hmass : delta*(N : Real) ≤ (P.carrier.card : Real)) : localProgressionAnchorDensity P delta ≤ 1 := by
  have hz : (0 : ZMod N) ∈ (centeredProgressionShrink P 1024).carrier :=
    (centered_progression_mem_iff _ 0).mpr ⟨fun _ => 0,by simp,by simp⟩
  have h := local_progression_anchor_mass P hP hd hmass hz
  have hc : ((progressionBridgeSet P.carrier 0).card : Real) ≤ N := by
    exact_mod_cast (Finset.card_le_univ _).trans_eq (ZMod.card N)
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hn := h.trans hc
  exact (mul_le_mul_iff_left₀ hN).mp (by simpa only [one_mul] using hn)

end LeanProofs.GowersSzemeredi
