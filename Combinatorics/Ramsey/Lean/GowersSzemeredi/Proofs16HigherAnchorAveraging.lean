import GowersSzemeredi.Proofs16HigherAnchorRestriction

/-! One pair of global anchor functions realizes at least the average
number of good higher arrangements with distinct shifts. All retained
configurations and their additive shift relation are explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_anchors_from_distinct_arrangements {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N))
    (hH : ∀ p ∈ H, Function.Injective (higherArrangementShifts p)) :
    ∃ (x y : ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N)),
      H.card ≤ N^8*Q.card ∧
      ∀ a ∈ Q, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧ shiftAnchorArrangement x y a ∈ H := by
  obtain ⟨g,hg⟩ := exists_balanced_incidence_fiber H RealizesHigherArrangement (N^8)
    (fun p hp => higher_anchor_restriction_balance p (hH p hp))
  let R := H.filter (RealizesHigherArrangement g)
  let Q := R.image higherArrangementShifts
  have hcard : Q.card = R.card := Finset.card_image_of_injOn (higherArrangementShifts_injOn_realizations g H)
  refine ⟨fun a => (g a).1,fun a => (g a).2,Q,?_,?_⟩
  · rw [hcard]
    exact hg
  · intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hpH,hpG⟩ := Finset.mem_filter.mp hp
    refine ⟨higherArrangementShifts_additive p,hH p hpH,?_⟩
    rw [RealizesHigherArrangement.reconstruct g p hpG]
    exact hpH

theorem exists_dense_anchors_from_distinct_arrangements {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N))
    (hH : ∀ p ∈ H, Function.Injective (higherArrangementShifts p)) {kappa : Real}
    (hmass : kappa*(N : Real)^11 ≤ H.card) :
    ∃ (x y : ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N)),
      kappa*(N : Real)^3 ≤ Q.card ∧
      ∀ a ∈ Q, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧ shiftAnchorArrangement x y a ∈ H := by
  obtain ⟨x,y,Q,hcount,hQ⟩ := exists_anchors_from_distinct_arrangements H hH
  refine ⟨x,y,Q,?_,hQ⟩
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply (mul_le_mul_iff_left₀ (pow_pos hn 8)).mp
  calc (kappa*(N : Real)^3)*(N : Real)^8 = kappa*(N : Real)^11 := by ring
    _ ≤ (H.card : Real) := hmass
    _ ≤ (Q.card : Real)*(N : Real)^8 := by
      exact_mod_cast (show H.card ≤ Q.card*N^8 by simpa only [Nat.mul_comm] using hcount)

end LeanProofs.GowersSzemeredi
