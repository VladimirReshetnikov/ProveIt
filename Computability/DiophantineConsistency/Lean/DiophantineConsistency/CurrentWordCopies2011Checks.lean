import DiophantineConsistency.CurrentWordCopies2011

namespace DiophantineConsistency.CurrentWordCopies2011Checks

open CurrentWordCopies2011 CurrentWordConstruction2011 CurrentWordClause2011
  CurrentMasks2011 WangTiles942Periodic

set_option Elab.async false
set_option maxRecDepth 10000

-- Whole-cell translation includes an arbitrary number of complete periods.
example {N : ℕ} [NeZero N] (j : ZMod N) (s : ℕ) :
    base (j-(s : ZMod N)) = base j-((2011*s : ℕ) : ZMod (N*2011)) :=
  base_sub_stride j s

example (j : ZMod 1) : base (j-(17 : ZMod 1)) = base j := by
  congr 1
  exact Subsingleton.elim _ _

-- The independently supplied dummy is transported to cell j-s, not j+s.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942)
    (dummy marker : ZMod N → ℕ) (s : ℕ) (j : ZMod N) :
    CurrentWordConstruction2011.word a dummy marker
      (base j+977-((2011*s : ℕ) : ZMod (N*2011))) = dummy (j-(s : ZMod N)) := by
  simpa only [ite_true,Nat.cast_ofNat] using
    word_shift_at_base a dummy marker s j 977 (by decide)

-- No matching premise is needed for the marker identity at zero stride.
example (a : ZMod 1 → Fin 942) (dummy : ZMod 1 → ℕ) (j : ZMod 1) :
    constructedWord a dummy 0 (base j+1004) = constructedWord a dummy 0 (base j) := by
  simpa only [Nat.mul_zero,Nat.cast_zero,sub_zero] using marker_pair a dummy 0 j

-- Nor is there a Boolean-dummy restriction on the exact marker pair.
example (a : ZMod 1 → Fin 942) (j : ZMod 1) :
    constructedWord a (fun _ => 7) 17
      (base j+1004-((2011*17 : ℕ) : ZMod (1*2011))) =
        constructedWord a (fun _ => 7) 17 (base j) := marker_pair a _ 17 j

private def threeTiles (j : ZMod 3) : Fin 942 := if j = 0 then 0 else 1
private def wrongMarker (j : ZMod 3) : ℕ := (decide (threeTiles (j-1) = 0)).toNat

-- A concrete sign challenge: the correct marker source is1, the same
-- literal source with the opposite marker sign is0. No tiling is asserted.
example : constructedWord threeTiles (fun _ => 0) 1
    (base (0 : ZMod 3)+1004-2011) = 1 := by
  have hp := marker_pair threeTiles (fun _ => 0) 1 (0 : ZMod 3)
  simp only [Nat.mul_one,Nat.cast_ofNat] at hp
  rw [hp]
  change CurrentWordConstruction2011.word threeTiles (fun _ => 0)
    (shiftedStartMarker threeTiles 1) (base 0) = 1
  have hb : base (0 : ZMod 3) = 0 := by simp [base]
  rw [hb,word_origin]
  rfl

example : CurrentWordConstruction2011.word threeTiles (fun _ => 0) wrongMarker
    (base (0 : ZMod 3)+1004-2011) = 0 := by
  have hp := word_shift_at_base threeTiles (fun _ => 0) wrongMarker 1 (0 : ZMod 3) 1004 (by decide)
  simp only [Nat.mul_one,Nat.cast_ofNat,show (1004 : ℕ) ≠ 977 by decide,
    ite_false,ite_true,Nat.cast_one] at hp
  rw [hp]
  decide

-- The physical field orientation is retained in both literal pair results.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (s : ℕ) (ha : MarkedWord N (s : ℤ) a) (j : ZMod N) :
    (∀ i : Fin 9, constructedWord a dummy s (base j+((942+i.val : ℕ) : ZMod (N*2011))) =
      constructedWord a dummy s
        (base j+((960+i.val : ℕ) : ZMod (N*2011))-((2011*s : ℕ) : ZMod (N*2011)))) ∧
    (∀ i : Fin 8, constructedWord a dummy s (base j+((969+i.val : ℕ) : ZMod (N*2011))) =
      constructedWord a dummy s
        (CurrentAdjacency2011.previousCell (base j)+((978+i.val : ℕ) : ZMod (N*2011)))) :=
  ⟨south_pair a dummy s ha j,horizontal_pair a dummy s ha j⟩

-- A normalization is actually constructed from the marked word; no mask,
-- pair equality, incoming-zero premise or given carry is requested.
example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s : ℕ) (ha : MarkedWord N (s : ℤ) a) :
    ∃ k digits : ZMod (N*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (constructedWord a dummy s) (displacement s) k digits ∧
      ∀ j, digits (base j+1004) &&& CurrentHighDigits2011.maskDigits (base j+1004) = 0 := by
  obtain ⟨k,digits,hf,_,_,hm⟩ := exists_copy_normalization a dummy hd s ha
  exact ⟨k,digits,hf,hm⟩

#print axioms constructed_boolean
#print axioms constructed_support
#print axioms base_sub_stride
#print axioms word_shift_at_base
#print axioms word_shift_data
#print axioms south_pair
#print axioms horizontal_pair
#print axioms marker_pair
#print axioms normalized_low_digit
#print axioms south_mask_pass
#print axioms horizontal_mask_pass
#print axioms marker_mask_pass
#print axioms copy_masks
#print axioms exists_copy_normalization

end DiophantineConsistency.CurrentWordCopies2011Checks
