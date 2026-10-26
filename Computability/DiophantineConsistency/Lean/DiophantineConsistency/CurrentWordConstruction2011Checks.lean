import DiophantineConsistency.CurrentWordConstruction2011

namespace DiophantineConsistency.CurrentWordConstruction2011Checks

open WangTiles942 CurrentMasks2011 CurrentCellLabels2011 CurrentCellConstruction2011
open CurrentWordConstruction2011 CurrentCellTranslation2011 CurrentCellCycle2011

set_option Elab.async false
set_option maxRecDepth 10000

-- The last canonical cell retains its last field, then wraps exactly.
example : (base (1 : ZMod 2)+(2010 : ZMod (2*2011))).val = 4021 := by decide
example : base (1 : ZMod 2)+(2011 : ZMod (2*2011)) = 0 := by decide

-- One full modulus returns the marker slot to the origin cell.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ) :
    word a dummy marker ((N*2011+1004 : ℕ) : ZMod (N*2011)) = marker 0 := by
  simpa only [show (1004 : ℕ) ≠ 977 by decide,ite_false,ite_true,ZMod.natCast_self] using
    word_at_nat_base a dummy marker N 1004 (by decide)

-- Arbitrarily many whole periods also work for the N=1 edge case.
example (a : ZMod 1 → Fin 942) (dummy marker : ZMod 1 → ℕ) :
    word a dummy marker ((17*2011+977 : ℕ) : ZMod (1*2011)) = dummy 0 := by
  simpa only [ite_true,Nat.cast_ofNat,show (17 : ZMod 1) = 0 from Subsingleton.elim _ _] using
    word_at_nat_base a dummy marker 17 977 (by decide)

example (a : ZMod 1 → Fin 942) (dummy marker : ZMod 1 → ℕ) :
    copiedWord (word a dummy marker) 0 = complementedTile (a 0) := by
  have h := word_copiedWord a dummy marker 0
  simpa only [base,ZMod.val_zero,Nat.zero_mul,Nat.cast_zero] using h

-- Independent Boolean control maps preserve all literal physical support.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942)
    (dummy marker : ZMod N → ℕ) (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) :
    (∀ k, word a dummy marker k ≤ 1) ∧
      (∀ k, k.val%2011 ∉ lowSupport → word a dummy marker k = 0) :=
  ⟨word_boolean a dummy marker hd hm,word_support a dummy marker⟩

example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942)
    (dummy marker : ZMod N → ℕ) (b : Cell N) :
    Selected (selectorValue (word a dummy marker) b) (a (coordinate b)) ∧
      copiedWord (word a dummy marker) b = complementedTile (a (coordinate b)) :=
  ⟨(word_cell_data a dummy marker b).1,(word_cell_data a dummy marker b).2.1⟩

example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942)
    (dummy marker : ZMod N → ℕ) (s : ℤ)
    (ha : WangTiles942Periodic.MarkedWord N s a) : word a dummy marker 0 = 1 :=
  word_origin_of_marked a dummy marker s ha

-- Non-Start at the origin gives zero even when both control maps are one.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (ha : a 0 ≠ 0) :
    word a (fun _ => 1) (fun _ => 1) 0 = 0 := by
  rw [word_origin,if_neg ha]

private def threeTiles (j : ZMod 3) : Fin 942 := if j = 0 then 0 else 1

-- The optional marker definition uses addition of stride, as printed;
-- this is an algebraic sign check, not a temporal-copy correctness claim.
example : shiftedStartMarker threeTiles 1 2 = 1 ∧
    shiftedStartMarker threeTiles 1 1 = 0 := by decide

#print axioms word_boolean
#print axioms word_support
#print axioms base_add_val
#print axioms base_add_field
#print axioms base_add_index
#print axioms word_at_base
#print axioms base_natCast
#print axioms word_at_nat_base
#print axioms word_data
#print axioms word_dummy
#print axioms word_marker
#print axioms word_selected
#print axioms word_copiedWord
#print axioms word_selectorPayload
#print axioms word_selectorCount
#print axioms base_eq_coordinate
#print axioms word_at_cell
#print axioms word_cell_data
#print axioms word_origin
#print axioms word_origin_of_marked
#print axioms shiftedStartMarker_boolean
#print axioms shiftedStartMarker_eq_one

end DiophantineConsistency.CurrentWordConstruction2011Checks
