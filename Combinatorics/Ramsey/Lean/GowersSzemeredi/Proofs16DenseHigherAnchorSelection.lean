import GowersSzemeredi.Proofs16HigherShiftCollisionCount

/-! Discarding repeated shifts costs at most `4*N^10`. For sufficiently
large modulus, half of a positive density remains for exact anchor averaging. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem higher_distinct_arrangements_mass {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) {kappa : Real}
    (hmass : kappa*(N : Real)^11 ≤ H.card) (hN : 8 ≤ kappa*(N : Real)) :
    (kappa/2)*(N : Real)^11 ≤ (H.filter fun p => Function.Injective (higherArrangementShifts p)).card := by
  have hbad : ((H.filter fun p => ¬ Function.Injective (higherArrangementShifts p)).card : Real) ≤
      4*(N : Real)^10 := by exact_mod_cast higher_repeated_shifts_card_le H
  have hsmall : 4*(N : Real)^10 ≤ (kappa/2)*(N : Real)^11 := by
    calc 4*(N : Real)^10 = (8/2)*(N : Real)^10 := by ring
      _ ≤ (kappa*(N : Real)/2)*(N : Real)^10 :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hN (by norm_num)) (by positivity)
      _ = (kappa/2)*(N : Real)^11 := by ring
  have hpart : ((H.filter fun p => Function.Injective (higherArrangementShifts p)).card : Real)+
      (H.filter fun p => ¬ Function.Injective (higherArrangementShifts p)).card = H.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := H) (fun p => Function.Injective (higherArrangementShifts p))
  nlinarith only [hpart,hbad,hsmall,hmass]

theorem exists_dense_anchors_from_arrangements {N : Nat} [NeZero N]
    (H : Finset (HigherArrangementParameter N)) {kappa : Real}
    (hmass : kappa*(N : Real)^11 ≤ H.card) (hN : 8 ≤ kappa*(N : Real)) :
    ∃ (x y : ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N)),
      (kappa/2)*(N : Real)^3 ≤ Q.card ∧
      ∀ a ∈ Q, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧ shiftAnchorArrangement x y a ∈ H := by
  let H' := H.filter fun p => Function.Injective (higherArrangementShifts p)
  obtain ⟨x,y,Q,hQ,hrealize⟩ := exists_dense_anchors_from_distinct_arrangements H'
    (fun p hp => (Finset.mem_filter.mp hp).2) (higher_distinct_arrangements_mass H hmass hN)
  exact ⟨x,y,Q,hQ,fun a ha => ⟨(hrealize a ha).1,(hrealize a ha).2.1,
    (Finset.mem_filter.mp (hrealize a ha).2.2).1⟩⟩

end LeanProofs.GowersSzemeredi
