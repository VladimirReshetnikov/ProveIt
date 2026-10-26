import DiophantineConsistency.CurrentCellConstruction2011

namespace DiophantineConsistency.CurrentCellConstruction2011Checks

open WangTiles942 CurrentMasks2011 CurrentCellLabels2011 CurrentCellConstruction2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

-- Prefix reconstruction includes the empty prefix and discards high bits.
example (m : ℕ) : binaryWord (bitDigit m) 0 = 0 := by
  rw [binaryWord_bitDigit]
  simp [Nat.mod_one]

example : binaryWord (bitDigit 1023) 9 = 511 := by
  rw [binaryWord_bitDigit]
  decide

example (i : Fin 942) : Selected
    (fun j => cell i ⟨physicalPosition j, (physicalPosition_lt j).trans (by decide)⟩) i :=
  localSelected i

example (i : Fin 942) : cell i ⟨977,by decide⟩ = 0 ∧
    cell i ⟨1004,by decide⟩ = 0 := ⟨localDigit_dummy i,localDigit_marker i⟩

example (i : Fin 942) : localDigit i 951 = 0 ∧ localDigit i 986 = 0 := by
  constructor <;> apply localDigit_support <;>
    simp only [lowSupport_def,Finset.mem_union,Finset.mem_range,Finset.mem_Ico,
      Finset.mem_singleton] <;> omega

-- The actual Start has West2 and East3, so its low control bits differ.
-- Interchanging the packed East/West blocks would fail these statements.
example : localDigit 0 978 = 1 ∧ localDigit 0 969 = 0 := by
  have hw := localDigit_west 0 0 (by decide)
  have he := localDigit_east 0 0 (by decide)
  norm_num only [Nat.add_zero,start_zero,bitDigit] at hw he
  exact ⟨hw,he⟩

example : localDigit 0 943 = 1 ∧ localDigit 0 942 = 0 := by
  have h1 := localDigit_south 0 1 (by decide)
  have h0 := localDigit_south 0 0 (by decide)
  norm_num only [Nat.add_zero,start_zero,bitDigit] at h1 h0
  exact ⟨h1,h0⟩

example : cell 0 ⟨0,by decide⟩ = 1 := literalStart _ rfl

example (i : Fin 942) :
    (2 * (∑ j : Fin 942, localDigit i (physicalPosition j)) +
      2048 * (localSelectorPayload i + localCopiedWord i) + localDigit i 1) &&&
        DoubledClause2011.mask = 0 := by
  rw [cellClauseBalance]
  exact (cellClauseMasked i).1

private def singleCell (i : Fin 942) (k : ZMod 2011) : ℕ := localDigit i k.val

private theorem singleCell_cast (i : Fin 942) (e : ℕ) (he : e < 2011) :
    singleCell i (e : ZMod 2011) = localDigit i e := by
  simp only [singleCell,ZMod.val_natCast,Nat.mod_eq_of_lt he]

-- The local data bind to the existing cyclic definitions, including N=1.
example (i : Fin 942) : copiedWord (N := 1) (singleCell i) 0 = complementedTile i := by
  apply copiedWord_of_local
  intro e he _
  simpa only [zero_add] using singleCell_cast i e (by omega)

example (i : Fin 942) : Selected (selectorValue (N := 1) (singleCell i) 0) i := by
  apply selected_of_local
  intro e he _
  simpa only [zero_add] using singleCell_cast i e (by omega)

example (i : Fin 942) : selectorPayload (N := 1) (singleCell i) 0 =
    1 + packedTile (tile i) := by
  have h : Selected (selectorValue (N := 1) (singleCell i) 0) i := by
    apply selected_of_local
    intro e he _
    simpa only [zero_add] using singleCell_cast i e (by omega)
  exact h.weighted_sum (fun j => 1+packedTile (tile j))

-- Label recovery is unchanged by either separate global control slot.
-- No Boolean bound on these two values is needed for this word identity.
example (i : Fin 942) (dummy marker : ℕ) :
    copiedWord (N := 1)
      (fun k => if k.val = 977 then dummy else if k.val = 1004 then marker
        else localDigit i k.val) 0 = complementedTile i := by
  apply copiedWord_of_local
  intro e he hd
  simp only [zero_add,ZMod.val_natCast,Nat.mod_eq_of_lt (show e < 2011 by omega),
    if_neg hd,if_neg (show e ≠ 1004 by omega)]

#print axioms bitDigit_eq_testBit
#print axioms binaryWord_bitDigit
#print axioms cell_boolean
#print axioms cell_support
#print axioms localSelected
#print axioms localSelectorPayload_eq
#print axioms localBinaryWords
#print axioms localCopiedWord_eq
#print axioms cellClauseBalance
#print axioms cellClauseMasked
#print axioms literalStart
#print axioms startLabelWords
#print axioms copiedWord_of_local
#print axioms selected_of_local
#print axioms selectorPayload_of_local

end DiophantineConsistency.CurrentCellConstruction2011Checks
