import DiophantineConsistency.CurrentTileColors2011

namespace DiophantineConsistency.CurrentTileColors2011Checks

open CurrentPolynomialWindow2011 CurrentCellLabels2011 CurrentTileColors2011

set_option Elab.async false

variable {N : ℕ} [NeZero (N*2011)]

/-- Field alignment permits zero displacement abstractly. The literal
Start and actual matching, rather than divisibility alone, exclude it. -/
example : (0 : ℕ) % 47 = 0 ∧ (0/47 : ℕ) % 2011 = 0 := by decide

example : (WangTiles942.tile 0).south ≠ (WangTiles942.tile 0).north := by
  rw [WangTiles942.start_zero]
  decide

example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N*2011) → ℕ) (h : Facts v N x c carry digits)
    (b : ZMod (N*2011)) (hb : b.val % 2011 = 0) (i j : Fin 942)
    (hi : selectorValue c b i = 1)
    (hj : selectorValue c (CurrentAdjacency2011.previousCell b) j = 1) :
    (WangTiles942.tile i).east = (WangTiles942.tile j).west :=
  facts_horizontal_colors v x c carry digits h b hb i j hi hj

/-- Any full-word-period displacement is excluded, even when its natural
representative is positive or much larger than the word. -/
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N*2011) → ℕ) (h : Facts v N x c carry digits) :
    ¬ (N*2011) ∣
      ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47*(N*2011))/47 := by
  intro hd
  apply facts_temporal_shift_nonzero v x c carry digits h
  exact (CharP.cast_eq_zero_iff (ZMod (N*2011)) (N*2011) _).mpr hd

#print axioms binaryWord_congr
#print axioms facts_selected_labels
#print axioms facts_horizontal_colors
#print axioms facts_temporal_colors
#print axioms facts_temporal_shift_nonzero

end DiophantineConsistency.CurrentTileColors2011Checks
