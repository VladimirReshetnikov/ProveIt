import CompactLowByteWindow

/-! Draft: a parameterized byte run after the highest support index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowByteTail
open CompactLowByteWindow

theorem support_le (i : ℕ) (hi : i ∈ CompactConcreteMask.support) : i ≤ 3296 := by
  simp only [CompactConcreteMask.support, Finset.mem_sdiff, Finset.mem_union,
    Finset.mem_range, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton] at hi
  omega

theorem late_digit (i : ℕ) (hlo : 3297 ≤ i) (hhi : i < 8807) :
    PaddedRadixDigits.digit lowDigits i = 2^67 - 1 := by
  rw [padded_digit, if_pos hhi]
  have hs : i ∉ CompactConcreteMask.support := by
    intro h
    have hh := support_le i h
    omega
  have hsp : i ≠ 1063 := by omega
  simp [CompactListMask.digit, hsp, hs]

theorem interior_digits (j : ℕ) (hlo : 27613 ≤ j) (hhi : j < 73751) :
    PaddedRadixDigits.digit lowDigits ((8*j)/67) = 2^67 - 1 ∧
    PaddedRadixDigits.digit lowDigits ((8*j)/67+1) = 2^67 - 1 := by
  have h0 : 3297 ≤ (8*j)/67 := by omega
  have h1 : (8*j)/67 + 1 < 8807 := by omega
  exact ⟨late_digit _ h0 (by omega), late_digit _ (by omega) h1⟩

theorem all_one_window (r : ℕ) (hr : r < 67) :
    ((2^67-1)/2^r + (2^67-1)*2^(67-r)) % 256 = 255 := by
  interval_cases r <;> norm_num

theorem interior_byte (j : ℕ) (hlo : 27613 ≤ j) (hhi : j < 73751) :
    (CompactSymbolicPorts.lowNat / 2^(8*j)) % 256 = 255 := by
  rw [low_byte]
  obtain ⟨h0,h1⟩ := interior_digits j hlo hhi
  rw [h0,h1]
  exact all_one_window _ (Nat.mod_lt _ (by decide))

#print axioms CompactLowByteTail.interior_byte
end CompactLowByteTail
