import GowersSzemeredi.Proofs16DifferenceProgressionMaps

/-! Select anchors in a prescribed tiny core. Its source-agreement data
are preserved because no new core or representatives are chosen. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_prescribed_difference_anchors {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper) (C : Finset (ZMod N))
    {delta : Real} (hdelta : 0 < delta) (hmass : delta*N ≤ (Q.carrier.card : Real))
    (hloss : (((centeredProgressionShrink Q 256).carrier \ C).card : Real) ≤ delta*N/(16*(1024 : Real)^Q.rank)) :
    ∃ v : ZMod N → ZMod N, ∀ a ∈ (centeredProgressionShrink Q 1024).carrier,
      v a ∈ C ∧ v a+a ∈ C ∧ delta*N/(2*(1024 : Real)^Q.rank) ≤ ((progressionBridgeSet C a).card : Real) := by
  have hanchors := fun a ha => progression_difference_anchor_mass Q hQ C hdelta hmass hloss (a := a) ha
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hpos : 0 < delta*N/(2*(1024 : Real)^Q.rank) := by positivity
  have hex : ∀ a : ZMod N, ∃ u : ZMod N,
      a ∈ (centeredProgressionShrink Q 1024).carrier → u ∈ C ∧ u+a ∈ C := by
    intro a
    by_cases ha : a ∈ (centeredProgressionShrink Q 1024).carrier
    · have hp : (0 : Real) < (progressionBridgeSet C a).card := hpos.trans_le (hanchors a ha)
      obtain ⟨u,hu⟩ := Finset.card_pos.mp (by exact_mod_cast hp)
      exact ⟨u,fun _ => Finset.mem_filter.mp hu⟩
    · exact ⟨0,fun h => False.elim (ha h)⟩
  choose v hv using hex
  exact ⟨v,fun a ha => ⟨(hv a ha).1,(hv a ha).2,hanchors a ha⟩⟩

end LeanProofs.GowersSzemeredi
