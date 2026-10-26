import DiophantineConsistency.CurrentMarkedWindow2011

namespace DiophantineConsistency.CurrentMarkedWindow2011Checks

open CurrentMarkedWindow2011 CurrentPolynomialWindow2011 CurrentOccupation2011
  CurrentCellLabels2011 CurrentCellTranslation2011 CurrentCellCycle2011
  WangTiles942 WangTiles942Periodic

set_option Elab.async false
set_option maxRecDepth 10000

-- The stride is the exact original quotient, not a chosen or reduced value.
example (v : Fin 14 → ℤ) (N : ℕ) : stride v N =
    (((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
      47*(N*2011))/47)/2011 := rfl

variable {N : ℕ} [NeZero (N * 2011)]

local instance (priority := 10) : NeZero N := ⟨Nat.ne_of_gt CurrentCellCycle2011.cellCount_pos⟩

-- Every other selector is zero in the very same original physical cell.
example (c : ZMod (N * 2011) → ℕ) (ho : ∀ b : Cell N, Occupied c b)
    (j : ZMod N) (i : Fin 942) (hi : i ≠ assignment c ho j) :
    selectorValue c ((coordinate.symm j : Cell N) : ZMod (N*2011)) i = 0 :=
  (assignment_selected c ho j).2 i hi

-- Facts are the sole native input to the actual marked-word endpoint.
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    ∃ a : ZMod N → Fin 942,
      (∀ j, Selected (selectorValue c ((coordinate.symm j : Cell N) : ZMod (N*2011))) (a j)) ∧
      MarkedWord N (stride v N : ℤ) a ∧ (stride v N : ZMod N) ≠ 0 ∧ 0 < stride v N :=
  facts_marked_assignment v x c carry digits h

-- The existing signed pullback gives the true East and next-row orientation
-- for this selected assignment, without a machine or rectangular premise.
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (p t : ℤ) :
    let a := assignment c (facts_occupied v x c carry digits h)
    (plane N (stride v N : ℤ) a (p+1) t).west =
      (plane N (stride v N : ℤ) a p t).east ∧
    (plane N (stride v N : ℤ) a p (t+1)).north =
      (plane N (stride v N : ℤ) a p t).south := by
  have hm := facts_marked_word v x c carry digits h
  exact ⟨plane_east_matching hm p t, plane_time_matching hm p t⟩

-- A one-cell actual window is excluded by Start's unequal temporal colors;
-- the earlier generic one-cell coordinate and occupation lemmas stay valid.
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (1 * 2011) → ℕ) (h : Facts v 1 x c carry digits) : False := by
  exact facts_stride_nonzero v x c carry digits h (Subsingleton.elim _ _)

example (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v polynomial = 0) :
    ∃ N, ∃ hN : 0 < N, MarkedWindow v N hN :=
  polynomial_zero_marked_window v hv hz

#print axioms assignment_selected
#print axioms previous_coordinate_base
#print axioms temporal_coordinate_base
#print axioms facts_stride_nonzero
#print axioms facts_stride_positive
#print axioms facts_assignment_zero
#print axioms facts_marked_word
#print axioms facts_marked_assignment
#print axioms polynomial_zero_marked_window

end DiophantineConsistency.CurrentMarkedWindow2011Checks
