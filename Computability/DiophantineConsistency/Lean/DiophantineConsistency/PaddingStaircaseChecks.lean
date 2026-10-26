import DiophantineConsistency.PaddingStaircase

/-!
# Focused staircase checks

The negative examples preserve the exact physical bit positions: a final
test alone is insufficient, the small additive budget matters, and the
low clause mask can hide a count of 512 if reduction is allowed to wrap.
-/

namespace DiophantineConsistency.PaddingStaircaseChecks

open PaddingStaircase

theorem first_hit (u : ℕ) (hu : u ≤ 2) : (2 * 4 + u) &&& 8 ≠ 0 := by
  intro h
  have hf := (bit3_mask_iff _).mp h
  rw [four_rejected u hu] at hf
  contradiction

theorem final_test_is_insufficient :
    (2 * 8).testBit 3 = false ∧ (2 * 4).testBit 3 = true := by decide

theorem additive_bound_matters : (2 * 4 + 8).testBit 3 = false := by decide

theorem multiples_of_sixteen (p u r : ℕ) :
    (16 * r + 2 * p + u).testBit 3 = (2 * p + u).testBit 3 := by
  apply bit3_eq_of_mod16
  omega

theorem numeric_margin : 2 * 462 + 57 + 1 + 1024 = 2006 ∧ 2006 < 2048 := by decide

theorem wrap_counterexample :
    2 * 512 + 1024 = 2048 ∧
    (2 * 512 + 1024) &&& 2044 = 0 ∧ 1 < (512 : ℕ) := by decide

theorem occupied_clause :
    (2 ^ 45 + 3) % 2048 = (2 * 1 + 0 + 1 + 0) % 2048 ∧
    (2 ^ 45 + 3) &&& (2 ^ 45 - 4) = 0 := by decide

example (k b t clause : ℕ) (hk : k ≤ 57) (hb : b ≤ 1) (ht : t ≤ 1024)
    (hresidue : clause % 2048 = (2 * 462 + k + b + t) % 2048) :
    clause &&& (2 ^ 45 - 4) ≠ 0 := by
  intro hmask
  have h := count_le_one_of_clause (by decide : 462 ≤ 462) hk hb ht hresidue hmask
  omega

#print axioms prefix_le_three
#print axioms prefix_le_three_of_masks
#print axioms total_le_462
#print axioms low_mask_iff
#print axioms count_le_one_of_clause
#print axioms total_le_one_of_masks
#print axioms first_hit
#print axioms wrap_counterexample

end DiophantineConsistency.PaddingStaircaseChecks
