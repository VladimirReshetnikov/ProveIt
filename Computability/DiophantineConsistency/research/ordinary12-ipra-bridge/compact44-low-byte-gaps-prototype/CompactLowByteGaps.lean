import CompactLowByteTail

/-! Draft: parameterized all-one windows in six sparse-support gaps. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowByteGaps
open CompactLowByteWindow CompactLowByteTail

theorem free_digit (i : ℕ) (hi : i < 8807) (hs : i ∉ CompactConcreteMask.support) :
    PaddedRadixDigits.digit lowDigits i = 2^67 - 1 := by
  rw [padded_digit, if_pos hi]
  have hsp : i ≠ 1063 := by
    intro h
    apply hs
    rw [h]
    exact CompactConcreteMask.special_mem
  simp [CompactListMask.digit, hsp, hs]

def inGap (j : ℕ) : Prop :=
  (7898 ≤ j ∧ j < 8225) ∨ (8317 ≤ j ∧ j < 8392) ∨
  (8643 ≤ j ∧ j < 8895) ∨ (8920 ≤ j ∧ j < 9163) ∨
  (9179 ≤ j ∧ j < 18375) ∨ (18392 ≤ j ∧ j < 27596)

theorem gap_byte (j : ℕ) (hj : inGap j) :
    (CompactSymbolicPorts.lowNat / 2^(8*j)) % 256 = 255 := by
  have hhi : (8*j)/67 + 1 < 8807 := by
    unfold inGap at hj
    omega
  have hs0 : (8*j)/67 ∉ CompactConcreteMask.support := by
    intro hs
    simp only [CompactConcreteMask.support, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_range, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton] at hs
    unfold inGap at hj
    omega
  have hs1 : (8*j)/67 + 1 ∉ CompactConcreteMask.support := by
    intro hs
    simp only [CompactConcreteMask.support, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_range, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton] at hs
    unfold inGap at hj
    omega
  rw [low_byte, free_digit _ (by omega) hs0, free_digit _ hhi hs1]
  exact all_one_window _ (Nat.mod_lt _ (by decide))

#print axioms CompactLowByteGaps.gap_byte
end CompactLowByteGaps
