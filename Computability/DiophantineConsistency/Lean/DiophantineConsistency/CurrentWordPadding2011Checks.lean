import DiophantineConsistency.CurrentWordPadding2011

namespace DiophantineConsistency.CurrentWordPadding2011Checks

open CurrentWordPadding2011 CurrentWordConstruction2011 CurrentWordClause2011
  CurrentReflectedGeometry2011 CurrentMasks2011

set_option Elab.async false
set_option maxRecDepth 10000

-- The complete last padding field still refers only to selector positions.
example (e : CurrentKernel2011.Entry) : source 916 e ≤ 896 :=
  padding_source_le (by decide) e

-- At the earliest fields even an arbitrary numeric control map cannot
-- create a reflected input; no whole-word Boolean premise is needed.
example (a : ZMod 1 → Fin 942) :
    reflected (word a (fun _ => 7) (fun _ => 23)) (base (0 : ZMod 1)+1) = 0 := by
  exact reflected_zero_before_twenty _ (word_support a _ _) _ (base_aligned _) (by decide)

-- Bare1004 wraps into unsupported fields, including the last padding
-- field and N=1. This is an actual assembled-word statement.
example (a : ZMod 1 → Fin 942) (dummy marker : ZMod 1 → ℕ) :
    word a dummy marker (base (0 : ZMod 1)+916-1004) = 0 :=
  padding_marker_input_zero _ (word_support a dummy marker) _ (base_aligned _) 916 (by decide)

example (a : ZMod 2 → Fin 942) (dummy marker : ZMod 2 → ℕ) :
    word a dummy marker (base (1 : ZMod 2)+1-1004) = 0 :=
  padding_marker_input_zero _ (word_support a dummy marker) _ (base_aligned _) 1 (by decide)

-- Reflected residue 0/2 holds even with non-Boolean control values;
-- the controls are not sources of any reflected padding term.
example (a : ZMod 1 → Fin 942) :
    reflected (word a (fun _ => 7) (fun _ => 23)) (base (0 : ZMod 1)+916)%2048 = 0 ∨
    reflected (word a (fun _ => 7) (fun _ => 23)) (base (0 : ZMod 1)+916)%2048 = 2 :=
  assembled_reflected_residue a _ _ 0 916 (by decide)

-- The bit proof depends on the residue, not a false small-whole-digit
-- hypothesis. A lower bit would not be justified by the same bound.
example : (2048*1000000+5 : ℕ) &&& 8 = 0 :=
  bit3_clear_of_residue (by decide)
example : (4 : ℕ)%2048 ≤ 5 ∧ (4 : ℕ) &&& 4 ≠ 0 := by decide
example : (8 : ℕ) &&& 8 ≠ 0 := by decide

-- The actual mask is8 at both band endpoints, including the last cell.
example : CurrentHighDigits2011.maskDigits (base (0 : ZMod 1)+1) = 8 :=
  padding_mask _ (base_aligned _) 1 (by decide)
example : CurrentHighDigits2011.maskDigits (base (1 : ZMod 2)+916) = 8 :=
  padding_mask _ (base_aligned _) 916 (by decide)

-- All controls may be1 and the displacement may traverse many periods.
-- No horizontal/temporal matching or marked-origin premise is requested.
example (a : ZMod 1 → Fin 942) :
    CurrentCarryConstruction2011.raw (word a (fun _ => 1) (fun _ => 1))
      (displacement 17) (base (0 : ZMod 1)+916)%2048 ≤ 5 :=
  assembled_raw_residue a _ _ (fun _ => by decide) (fun _ => by decide) 17 0 916 (by decide)

-- Zero stride is also admitted, and the carry solution is constructed
-- before asserting any of the916 mask tests.
example (a : ZMod 1 → Fin 942) :
    ∃ k digits : ZMod (1*2011) → ℕ,
      CurrentCarryConstruction2011.Facts (word a (fun _ => 1) (fun _ => 1))
        (displacement 0) k digits ∧
      ∀ h : ℕ, 1 ≤ h → h ≤ 916 →
        digits (base (0 : ZMod 1)+(h : ZMod (1*2011))) &&&
          CurrentHighDigits2011.maskDigits (base (0 : ZMod 1)+(h : ZMod (1*2011))) = 0 := by
  obtain ⟨k,digits,hf,hm⟩ := exists_padding_normalization a (fun _ => 1) (fun _ => 1)
    (fun _ => by decide) (fun _ => by decide) 0
  exact ⟨k,digits,hf,hm 0⟩

#print axioms padding_source_le
#print axioms padding_reflected_residue
#print axioms padding_marker_input_zero
#print axioms padding_raw_residue
#print axioms bit3_clear_of_residue
#print axioms padding_mask
#print axioms assembled_reflected_residue
#print axioms assembled_raw_residue
#print axioms normalized_padding_residue
#print axioms padding_mask_pass
#print axioms exists_padding_normalization

end DiophantineConsistency.CurrentWordPadding2011Checks
