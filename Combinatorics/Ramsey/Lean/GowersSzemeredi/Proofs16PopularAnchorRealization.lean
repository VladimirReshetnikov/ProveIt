import GowersSzemeredi.Proofs16GlobalPopularAnchors

/-! Realized popular arrangements provide many bases for each actual
shift, and both chosen anchor bases lie in the supported core. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem shiftAnchorArrangement_shifts {N : Nat} (x y : ZMod N → ZMod N)
    (a : Fin 4 → ZMod N) (ha : a 0+a 1 = a 2+a 3) :
    higherArrangementShifts (shiftAnchorArrangement x y a) = a := by
  have h3 : a 0+a 1-a 2 = a 3 := by linear_combination ha
  funext j
  fin_cases j <;> dsimp [higherArrangementShifts,shiftAnchorArrangement]
  exact h3

theorem supported_shift_anchor_bases {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) (x y : ZMod N → ZMod N) (a : Fin 4 → ZMod N)
    (ha : a 0+a 1 = a 2+a 3)
    (hp : shiftAnchorArrangement x y a ∈ supportedHigherArrangements P) (j : Fin 4) :
    x (a j) ∈ columnShiftBases P (a j) ∧ y (a j) ∈ columnShiftBases P (a j) := by
  have hq := supported_higher_anchor_quadruple_mem P hp j
  have hP := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hq).1
  simp only [higherArrangementAnchorQuadruple,shiftAnchorArrangement_left_pair x y a ha,
    shiftAnchorArrangement_right_pair x y a ha,shiftAnchorPair] at hP
  exact ⟨Finset.mem_filter.mpr ⟨hP 1,hP 0⟩,Finset.mem_filter.mpr ⟨hP 3,hP 2⟩⟩

theorem popular_shift_anchor_bases {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) (x y : ZMod N → ZMod N) (a : Fin 4 → ZMod N) {t : Real}
    (ha : a 0+a 1 = a 2+a 3)
    (hp : shiftAnchorArrangement x y a ∈ popularSupportedHigherArrangements P t) (j : Fin 4) :
    t*N ≤ ((columnShiftBases P (a j)).card : Real) ∧
      x (a j) ∈ columnShiftBases P (a j) ∧ y (a j) ∈ columnShiftBases P (a j) := by
  obtain ⟨hP,hpopular⟩ := Finset.mem_filter.mp hp
  refine ⟨?_,supported_shift_anchor_bases P x y a ha hP j⟩
  simpa only [shiftAnchorArrangement_shifts x y a ha] using hpopular j

end LeanProofs.GowersSzemeredi
