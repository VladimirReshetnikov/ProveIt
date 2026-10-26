import DiophantineConsistency.CurrentOccupation2011

namespace DiophantineConsistency.CurrentOccupation2011Checks

open CurrentOccupation2011 CurrentPolynomialWindow2011 CurrentCellLabels2011
  CurrentCellTranslation2011 WangTiles942
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

-- The actual Start has strictly positive complemented horizontal colors.
example : 255 - (tile 0).west = 253 ∧ 255 - (tile 0).east = 252 := by
  rw [start_zero]
  decide

-- Eight-bit boundedness alone would permit a zero complement; the proof
-- instead uses the strict bound on every actual table entry.
example : (255 : ℕ) < 256 ∧ 255 - (255 : ℕ) = 0 := by decide

example (i : Fin 942) : 5 < 255 - (tile i).west ∧ 5 < 255 - (tile i).east := by
  obtain ⟨hw, he⟩ := WangTiles942Language.tile_horizontal_bound i
  omega

variable {N : ℕ} [NeZero (N * 2011)]

-- The selected tile is unique in each cell; no globally unique Start is assumed.
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : Cell N) : ∃! i : Fin 942, selectorValue c b i = 1 := by
  obtain ⟨i, hs⟩ := facts_occupied v x c carry digits h b
  exact ⟨i, hs.1, fun j hj => hs.unique j hj⟩

-- Abstract and physical selector counts describe the same actual word.
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : Cell N) : (∑ j : Fin 942, c ((b : ZMod (N * 2011)) + (j.val : ZMod (N * 2011)))) = 1 := by
  have hh := facts_selectorCount_eq_one v x c carry digits h b b.property
  rw [CurrentClause2011.selectorCount_eq_prefix, PaddingStaircase.prefixSum] at hh
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => c ((b : ZMod (N * 2011)) + (j : ZMod (N * 2011)))) 942]
  exact hh

-- The single-cell cycle is included without a separate N>1 hypothesis.
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (1 * 2011) → ℕ) (h : Facts v 1 x c carry digits)
    (b : Cell 1) : Occupied c b := facts_occupied v x c carry digits h b

example (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v polynomial = 0) :
    ∃ N, ∃ hN : 0 < N, OccupiedWindow v N hN :=
  polynomial_zero_occupied_window v hv hz

#print axioms horizontal_words
#print axioms occupied_west_positive
#print axioms facts_start_selected
#print axioms facts_next_occupied
#print axioms facts_occupied
#print axioms facts_selectorCount_eq_one
#print axioms polynomial_zero_occupied_window

end DiophantineConsistency.CurrentOccupation2011Checks
