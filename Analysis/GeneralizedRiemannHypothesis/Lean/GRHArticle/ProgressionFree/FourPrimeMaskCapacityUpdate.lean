import GRHArticle.ProgressionFree.FourPrimeMaskRows

/-!
# Updating a cached capacity after clearing a bit

The capacity on every other nine-bit row is fixed. Subtract the old
line capacity and add the new one, using the whole sum only at initialization.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

private def rowCapacity (q : Fin 4 → ℕ) (row mask : ℕ) : ℕ :=
  fourPrimeRowFactor q row *
    fourPrimeLineCapacity (q 0) (fourPrimeRowOtherGood row) (mask >>> (9*row))

private theorem clearGPBit_row_chunk_eq {mask i row : ℕ} (hne : row ≠ i/9) :
    ((clearGPBit mask i) >>> (9*row)) % 512 = (mask >>> (9*row)) % 512 := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (((clearGPBit mask i) >>> (9*row)) % 2^9).testBit j = ((mask >>> (9*row)) % 2^9).testBit j
  rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow]
  by_cases hj : j < 9
  · have h₀ : i ≠ 9*row+j := by
      intro h
      apply hne
      rw [h]
      omega
    simp [hj,Nat.testBit_shiftRight,testBit_clearGPBit,h₀]
  · simp [hj]

private theorem rowCapacity_clear_eq (q : Fin 4 → ℕ) (mask i row : ℕ) (hne : row ≠ i/9) :
    rowCapacity q row (clearGPBit mask i) = rowCapacity q row mask := by
  unfold rowCapacity fourPrimeLineCapacity
  rw [clearGPBit_row_chunk_eq hne]

private theorem maskCapacity_eq_sum (q : Fin 4 → ℕ) (mask : ℕ) :
    fourPrimeMaskCapacity q mask = ∑ row ∈ range 81, rowCapacity q row mask := rfl

/-- Update the cached sum by recomputing only the row of the cleared bit. -/
def fourPrimeMaskCapacityUpdate (q : Fin 4 → ℕ) (mask capacity i : ℕ) : ℕ :=
  let row := i/9
  if row < 81 then
    capacity - rowCapacity q row mask + rowCapacity q row (clearGPBit mask i)
  else capacity

/-- The single-row update preserves the exact cached upper bound. -/
theorem fourPrimeMaskCapacityUpdate_correct (q : Fin 4 → ℕ) (mask i : ℕ) :
    fourPrimeMaskCapacityUpdate q mask (fourPrimeMaskCapacity q mask) i =
      fourPrimeMaskCapacity q (clearGPBit mask i) := by
  let row := i/9
  change (if row < 81 then fourPrimeMaskCapacity q mask - rowCapacity q row mask +
    rowCapacity q row (clearGPBit mask i) else fourPrimeMaskCapacity q mask) = _
  simp only [maskCapacity_eq_sum]
  by_cases h : row < 81
  · rw [if_pos h]
    have hm : row ∈ range 81 := mem_range.mpr h
    have horig := sum_erase_add (range 81) (fun r ↦ rowCapacity q r mask) hm
    have hnew := sum_erase_add (range 81) (fun r ↦ rowCapacity q r (clearGPBit mask i)) hm
    have he :
        ∑ r ∈ (range 81).erase row, rowCapacity q r (clearGPBit mask i) =
          ∑ r ∈ (range 81).erase row, rowCapacity q r mask :=
      sum_congr rfl fun r hr ↦ rowCapacity_clear_eq q mask i r (mem_erase.mp hr).1
    rw [he] at hnew
    omega
  · rw [if_neg h]
    apply sum_congr rfl
    intro r hr
    symm
    apply rowCapacity_clear_eq
    have hR := mem_range.mp hr
    change ¬ i/9 < 81 at h
    omega

end GRHArticle.ProgressionFree
