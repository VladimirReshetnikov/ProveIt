import GowersSzemeredi.Proofs16UnpopularAnchorQuadruples

/-! Removing unpopular anchor shifts preserves a quantitative density
of supported higher arrangements. Every surviving shift has many bases. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def popularSupportedHigherArrangements {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) (t : Real) : Finset (HigherArrangementParameter N) :=
  (supportedHigherArrangements P).filter fun p =>
    ∀ j : Fin 4, t*N ≤ ((columnShiftBases P (higherArrangementShifts p j)).card : Real)

theorem higherArrangementAnchorQuadruple_shift {N : Nat}
    (p : HigherArrangementParameter N) (j : Fin 4) :
    higherArrangementAnchorQuadruple p j 0-higherArrangementAnchorQuadruple p j 1 =
      higherArrangementShifts p j := by
  rw [higherArrangementAnchorQuadruple_eq]
  simp

theorem avoiding_unpopular_anchor_quadruples_subset {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) (t : Real) :
    higherArrangementAvoidingBadData (supportedHigherArrangements P) ∅
      (unpopularAnchorQuadruples P t) ∅ ∅ ⊆ popularSupportedHigherArrangements P t := by
  intro p hp
  obtain ⟨hP,hq,-,-,-⟩ := (mem_higherArrangementAvoidingBadData _ _ _ _ _ p).mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hP,fun j => le_of_not_gt ?_⟩
  intro hlt
  apply hq j
  apply Finset.mem_filter.mpr
  exact ⟨supported_higher_anchor_quadruple_mem P hP j,
    by simpa only [higherArrangementAnchorQuadruple_shift] using hlt⟩

theorem popular_supported_higher_arrangements_dense {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) {alpha t : Real} (ha : 0 ≤ alpha)
    (hP : alpha*(N : Real) ≤ P.card) :
    (alpha^16-4*t^2)*(N : Real)^11 ≤ (popularSupportedHigherArrangements P t).card := by
  have h := higher_arrangements_avoiding_bad_data_mass (supportedHigherArrangements P) ∅
    (unpopularAnchorQuadruples P t) ∅ ∅
    (supported_higher_arrangements_dense P ha hP) (unpopular_anchor_quadruples_card_le P)
    (show ((∅ : Finset (Fin 8 → ZMod N)).card : Real) ≤ 0*(N : Real)^7 by simp)
    (show ((∅ : Finset (Fin 8 → ZMod N)).card : Real) ≤ 0*(N : Real)^7 by simp)
    (show ((∅ : Finset (HigherArrangementParameter N)).card : Real) ≤ 0*(N : Real)^11 by simp)
  have hc : ((higherArrangementAvoidingBadData (supportedHigherArrangements P) ∅
      (unpopularAnchorQuadruples P t) ∅ ∅).card : Real) ≤
      (popularSupportedHigherArrangements P t).card := by
    exact_mod_cast Finset.card_le_card (avoiding_unpopular_anchor_quadruples_subset P t)
  simpa only [sub_zero] using h.trans hc

end LeanProofs.GowersSzemeredi
