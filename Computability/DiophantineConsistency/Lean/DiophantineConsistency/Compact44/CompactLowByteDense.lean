import DiophantineConsistency.Compact44.CompactLowByteWindow

/-! Draft: periodic low-mask byte windows in the dense support region. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowByteDense
open CompactLowByteWindow

def denseWindow (r : ℕ) : ℕ :=
  if r = 0 then 254 else if 60 ≤ r then 255 - 2^(67-r) else 255

theorem dense_digit (i : ℕ) (hlo : 2 ≤ i) (hhi : i < 943) :
    PaddedRadixDigits.digit lowDigits i = 2^67 - 2 := by
  rw [padded_digit, if_pos (by omega)]
  have hs : i ∈ CompactConcreteMask.support := by
    simp only [CompactConcreteMask.support, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_range, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hsp : i ≠ 1063 := by omega
  simp [CompactListMask.digit, hsp, hs]

theorem dense_arithmetic (r : ℕ) (hr : r < 67) :
    ((2^67-2)/2^r + (2^67-2)*2^(67-r)) % 256 = denseWindow r := by
  interval_cases r <;> norm_num [denseWindow]

theorem dense_byte (j : ℕ) (hlo : 17 ≤ j) (hhi : j < 7890) :
    (CompactSymbolicPorts.lowNat / 2^(8*j)) % 256 = denseWindow ((8*j)%67) := by
  rw [low_byte]
  have h0 : 2 ≤ (8*j)/67 := by omega
  have h1 : (8*j)/67+1 < 943 := by omega
  rw [dense_digit _ h0 (by omega), dense_digit _ (by omega) h1]
  exact dense_arithmetic _ (Nat.mod_lt _ (by decide))

#print axioms CompactLowByteDense.dense_byte
end CompactLowByteDense
