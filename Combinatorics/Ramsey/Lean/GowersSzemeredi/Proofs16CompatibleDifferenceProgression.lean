import GowersSzemeredi.Proofs16DifferenceProgressionMaps

/-! Actual compatible difference maps on the final proper shrinking, from
local map data and the original selected-query exception bound. Every index
has quantitatively many tiny-core anchor pairs; no compatibility is assumed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The selected maps produce difference maps on the entire proper
progression `Q/1024`, with every quadruple compatible and both origins zero. -/
theorem exists_compatible_difference_progression_maps {N d K : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper)
    (T : ZMod N → Finset (ZMod N)) (F : ZMod N → ZMod N → ZMod N)
    {rho delta eta : Real} (hrho : 0 < rho) (hK : 0 < K) (hdelta : 0 < delta)
    (hmass : delta*N ≤ (Q.carrier.card : Real))
    (heta : eta ≤ delta^3/(1024*(65536 : Real)^Q.rank))
    (hdata : ∀ x ∈ Q.carrier, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (F x) ∧ F x 0 = 0)
    (hfail : ((progressionMapImageFailures Q.carrier T F rho K).card : Real) ≤ eta*(N : Real)^3) :
    let M := K*K*refinementKernelCap (4*d) (2*d) rho rho
    let H := M*M*refinementKernelCap (4*d) (2*d) (rho/2) (rho/2)
    let J := H^4*refinementKernelCap (8*d) (4*d) (rho/4) (rho/4)
    ∃ (C : Finset (ZMod N)) (v : ZMod N → ZMod N),
      C ⊆ (centeredProgressionShrink Q 256).carrier ∧ C.Nonempty ∧
      delta*N/(2*(512 : Real)^Q.rank) ≤ (C.card : Real) ∧
      (∀ a ∈ (centeredProgressionShrink Q 1024).carrier,
        v a ∈ C ∧ v a+a ∈ C ∧
          delta*N/(2*(1024 : Real)^Q.rank) ≤ ((progressionBridgeSet C a).card : Real)) ∧
      (∀ a ∈ (centeredProgressionShrink Q 1024).carrier,
        (differenceAnchorSpectrum T v a).card ≤ 2*d ∧
        IsFreimanLinearOn (bohr (differenceAnchorSpectrum T v a) rho) (differenceAnchorMap F v a) ∧
        differenceAnchorMap F v a 0 = 0) ∧
      (∀ y, differenceAnchorMap F v 0 y = 0) ∧
      (∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ C ∧ (q i).2 ∈ C) → pairedColumnIndex q = 0 →
        PairedColumnImageRelation T F (rho/8) J q) ∧
      ∀ a b c e : ZMod N, a ∈ (centeredProgressionShrink Q 1024).carrier →
        b ∈ (centeredProgressionShrink Q 1024).carrier → c ∈ (centeredProgressionShrink Q 1024).carrier →
        e ∈ (centeredProgressionShrink Q 1024).carrier → a-b = c-e →
          ColumnQuadImageRelation (differenceAnchorSpectrum T v) (differenceAnchorMap F v) (rho/8) J a b c e := by
  intro M H J
  obtain ⟨S,C,hS,hCeq,hloss,hCmass,hCne,h8⟩ := exists_progression_all_eight_image_core Q hQ T F
    hrho hK hdelta hmass heta (fun x hx => (hdata x hx).1) (fun x hx => (hdata x hx).2.1) hfail
  have hC : C ⊆ (centeredProgressionShrink Q 256).carrier := by
    rw [hCeq]
    exact Finset.inter_subset_right
  have hsub : (centeredProgressionShrink Q 256).carrier ⊆ (centeredProgressionShrink Q 16).carrier := by
    simpa only [centered_progression_shrink_comp, Nat.reduceMul] using
      centered_progression_shrink_subset (centeredProgressionShrink Q 16) 16
  have hmissing : (centeredProgressionShrink Q 256).carrier \ C ⊆ (centeredProgressionShrink Q 16).carrier \ S := by
    intro x hx
    obtain ⟨hxD,hxC⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_sdiff.mpr ⟨hsub hxD, ?_⟩
    intro hxS
    apply hxC
    rw [hCeq]
    exact Finset.mem_inter.mpr ⟨hxS,hxD⟩
  have hmissingR : (((centeredProgressionShrink Q 256).carrier \ C).card : Real) ≤
      ((centeredProgressionShrink Q 16).carrier \ S).card := by
    exact_mod_cast Finset.card_le_card hmissing
  have hanchors := fun a ha => progression_difference_anchor_mass Q hQ C hdelta hmass
    (hmissingR.trans hloss) (a := a) ha
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hanchorpos : 0 < delta*N/(2*(1024 : Real)^Q.rank) := by positivity
  have hex : ∀ a : ZMod N, ∃ u : ZMod N,
      a ∈ (centeredProgressionShrink Q 1024).carrier → u ∈ C ∧ u+a ∈ C := by
    intro a
    by_cases ha : a ∈ (centeredProgressionShrink Q 1024).carrier
    · have hpos : (0 : Real) < (progressionBridgeSet C a).card := hanchorpos.trans_le (hanchors a ha)
      obtain ⟨u,hu⟩ := Finset.card_pos.mp (by exact_mod_cast hpos)
      exact ⟨u,fun _ => Finset.mem_filter.mp hu⟩
    · exact ⟨0,fun h => False.elim (ha h)⟩
  choose v hv using hex
  have hCdata : ∀ x ∈ C, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (F x) ∧ F x 0 = 0 :=
    fun x hx => hdata x (centered_progression_shrink_subset Q 256 (hC hx))
  refine ⟨C,v,hC,hCne,hCmass,?_,?_,difference_anchor_index_zero F v,h8,?_⟩
  · intro a ha
    exact ⟨(hv a ha).1,(hv a ha).2,hanchors a ha⟩
  · intro a ha
    exact difference_anchor_map_data C T F v rho hCdata (hv a ha).1 (hv a ha).2
  · exact difference_progression_quad_images (centeredProgressionShrink Q 1024).carrier C T F v
      (rho/8) hv h8

end LeanProofs.GowersSzemeredi
