import DiophantineConsistency.SelectorBindingCoherence

/-! UNCOMPILED intended regression tests; not execution evidence. -/
namespace DiophantineConsistency.SelectorBindingCoherenceChecks
open CurrentMarkedWindow2011 CurrentPolynomialWindow2011 CurrentOccupation2011
  CurrentCellLabels2011 CurrentCellTranslation2011 CurrentCellCycle2011
  CurrentCellCoordinate2011 WangTiles942Periodic

variable {N : ℕ} [NeZero (N * 2011)]
local instance (priority := 10) : NeZero N :=
  ⟨Nat.ne_of_gt CurrentCellCycle2011.cellCount_pos⟩

-- Coherence concerns indices, not an assumed injection from tile colors.
example (c : ZMod (N * 2011) → ℕ) (ho : ∀ b : Cell N, Occupied c b)
    (a b : ZMod N → Fin 942)
    (ha : ∀ j, selectorValue c ((coordinate.symm j : Cell N) : ZMod (N * 2011)) (a j) = 1)
    (hb : ∀ j, selectorValue c ((coordinate.symm j : Cell N) : ZMod (N * 2011)) (b j) = 1) :
    a = b :=
  ((assignment_eq_iff_selector c ho a).mpr ha).trans
    ((assignment_eq_iff_selector c ho b).mpr hb).symm

-- Changing an occupation proof is already handled by Lean proof irrelevance;
-- this is not the novelty claimed by the assignment-index coherence theorem.
example (c : ZMod (N * 2011) → ℕ) (ho hp : ∀ b : Cell N, Occupied c b) :
    assignment c ho = assignment c hp := rfl

-- Generic coherence includes N=1, before Facts exclude an actual one-cell window.
example (c : ZMod (1 * 2011) → ℕ) (ho : ∀ b : Cell 1, Occupied c b)
    (a : ZMod 1 → Fin 942)
    (ha : ∀ j, selectorValue c ((coordinate.symm j : Cell 1) : ZMod (1 * 2011)) (a j) = 1) :
    a = assignment c ho := (assignment_eq_iff_selector c ho a).mpr ha

-- An alternative decoder still has Start at the same canonical zero coordinate.
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (a : ZMod N → Fin 942)
    (ha : ∀ j, selectorValue c ((coordinate.symm j : Cell N) : ZMod (N * 2011)) (a j) = 1) :
    a 0 = 0 := by
  rw [(assignment_eq_iff_selector c (facts_occupied v x c carry digits h) a).mpr ha]
  exact facts_assignment_zero v x c carry digits h

-- The actual stride and its nonzero residue are retained, not normalized away.
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (a : ZMod N → Fin 942)
    (ha : ∀ j, selectorValue c ((coordinate.symm j : Cell N) : ZMod (N * 2011)) (a j) = 1) :
    MarkedWord N (stride v N : ℤ) a ∧ (stride v N : ZMod N) ≠ 0 :=
  ⟨facts_marked_word_of_selector v x c carry digits h a ha,
    facts_stride_nonzero v x c carry digits h⟩

#print axioms assignment_eq_iff_selector
#print axioms facts_marked_word_of_selector
end DiophantineConsistency.SelectorBindingCoherenceChecks
