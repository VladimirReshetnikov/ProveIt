import DiophantineConsistency.CurrentMarkedWindow2011

/-!
# Candidate: the original selector word determines the entire assignment

UNCOMPILED against b310142330df89e48413c8fce62e7de223e1c7d5.
This additive API is not claimed to reduce the current source line count.
It identifies actual selected indices, not tiles inferred from their colors.
-/

namespace DiophantineConsistency.CurrentMarkedWindow2011

open CurrentPolynomialWindow2011 CurrentOccupation2011 CurrentCellLabels2011
  CurrentCellTranslation2011 CurrentCellCycle2011 CurrentCellCoordinate2011
  WangTiles942Periodic

set_option Elab.async false

variable {N : ℕ} [NeZero (N * 2011)]

local instance (priority := 10) : NeZero N :=
  ⟨Nat.ne_of_gt CurrentCellCycle2011.cellCount_pos⟩

/-- Any independently extracted assignment is the existing canonical
assignment exactly when its indices are selected in the same original word. -/
theorem assignment_eq_iff_selector (c : ZMod (N * 2011) → ℕ)
    (ho : ∀ b : Cell N, Occupied c b) (a : ZMod N → Fin 942) :
    a = assignment c ho ↔
      ∀ j, selectorValue c ((coordinate.symm j : Cell N) : ZMod (N * 2011)) (a j) = 1 := by
  constructor
  · rintro rfl j
    exact (assignment_selected c ho j).1
  · intro ha
    funext j
    exact (assignment_selected c ho j).unique _ (ha j)

/-- Correctness transports to another selector decoder without repeating
spatial/temporal coordinate transport or making a new choice of word. -/
theorem facts_marked_word_of_selector (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (a : ZMod N → Fin 942)
    (ha : ∀ j, selectorValue c ((coordinate.symm j : Cell N) : ZMod (N * 2011)) (a j) = 1) :
    MarkedWord N (stride v N : ℤ) a := by
  rw [(assignment_eq_iff_selector c (facts_occupied v x c carry digits h) a).mpr ha]
  exact facts_marked_word v x c carry digits h

end DiophantineConsistency.CurrentMarkedWindow2011
