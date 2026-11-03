import CompactLowByteRecipeData
import CompactLowBytePrefix
import CompactLowByteDense
import CompactLowByteDenseExtra
import CompactLowByteGaps
import CompactLowByteTail
import CompactLowByteBound
import RadixWindowReconstruction
import CompactLowByteBoundary01
import CompactLowByteBoundary02
import CompactLowByteBoundary03
import CompactLowByteBoundary04
import CompactLowByteBoundary05
import CompactLowByteBoundary06
import CompactLowByteBoundary07
import CompactLowByteBoundary08
import CompactLowByteBoundary09
import CompactLowByteBoundary10
import CompactLowByteBoundary11
import CompactLowByteBoundary12

/-! Draft: not an established result until compiled in a coherent provider. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
noncomputable section
namespace CompactLowByteAssembly
open CompactLowByteRecipeData
open CompactLowByteDense CompactLowByteDenseExtra CompactLowByteGaps
open CompactLowByteTail
attribute [local irreducible] bytes CompactSymbolicPorts.lowNat

theorem irregular_gap (j : ℕ) (hg : inGap j) : irregularByte j = 255 := by
  unfold irregularByte inGap at *
  split_ifs <;> omega

theorem irregular_tail (j : ℕ) (ht : 27613 ≤ j ∧ j < 73751) :
    irregularByte j = 255 := by
  unfold irregularByte
  split_ifs <;> omega

theorem point (j : ℕ) (hj : j < 73759) :
    byteAt j = (CompactSymbolicPorts.lowNat / 256^j) % 256 := by
  have hpow : (256:ℕ)^j = 2^(8*j) := by
    rw [show (256:ℕ) = 2^8 by norm_num, ← pow_mul]
  by_cases hp : j < 16
  · have hv : byteAt j = CompactLowBytePrefix.firstBytes.getD j 0 := by
      interval_cases j <;> norm_num [byteAt, denseIndex, irregularByte,
        CompactLowBytePrefix.firstBytes]
    rw [hv]
    exact CompactLowBytePrefix.prefix_windows j hp
  by_cases hd : 17 ≤ j ∧ j < 7890
  · have hdi : denseIndex j := by unfold denseIndex; omega
    have hj0 : j ≠ 0 := by omega
    rw [byteAt, if_neg hj0, if_pos hdi, hpow]
    exact (CompactLowByteDense.dense_byte j hd.1 hd.2).symm
  by_cases he : inDenseExtra j
  · have hdi : denseIndex j := by unfold denseIndex inDenseExtra at *; omega
    have hj0 : j ≠ 0 := by unfold inDenseExtra at he; omega
    rw [byteAt, if_neg hj0, if_pos hdi, hpow]
    exact (CompactLowByteDenseExtra.extra_dense_byte j he).symm
  by_cases hg : inGap j
  · have hdi : ¬ denseIndex j := by unfold denseIndex inGap at *; omega
    have hj0 : j ≠ 0 := by unfold inGap at hg; omega
    have hv : irregularByte j = 255 := irregular_gap j hg
    rw [byteAt, if_neg hj0, if_neg hdi, hv, hpow]
    exact (CompactLowByteGaps.gap_byte j hg).symm
  by_cases ht : 27613 ≤ j ∧ j < 73751
  · have hdi : ¬ denseIndex j := by unfold denseIndex; omega
    have hj0 : j ≠ 0 := by omega
    have hv : irregularByte j = 255 := irregular_tail j ht
    rw [byteAt, if_neg hj0, if_neg hdi, hv, hpow]
    exact (CompactLowByteTail.interior_byte j ht.1 ht.2).symm
  have hleft : (16 ≤ j ∧ j < 17) ∨
      (7890 ≤ j ∧ j < 7898) ∨
      (8225 ≤ j ∧ j < 8233) ∨
      (8308 ≤ j ∧ j < 8317) ∨
      (8392 ≤ j ∧ j < 8401) ∨
      (8468 ≤ j ∧ j < 8484) ∨
      (8635 ≤ j ∧ j < 8643) ∨
      (8895 ≤ j ∧ j < 8920) ∨
      (9163 ≤ j ∧ j < 9179) ∨
      (18375 ≤ j ∧ j < 18392) ∨
      (27596 ≤ j ∧ j < 27613) ∨
      (73751 ≤ j ∧ j < 73759) := by
    unfold inGap inDenseExtra at *
    omega
  rcases hleft with h | h | h | h | h | h | h | h | h | h | h | h
  · exact CompactLowByteBoundary01.windows j h.1 h.2
  · exact CompactLowByteBoundary02.windows j h.1 h.2
  · exact CompactLowByteBoundary03.windows j h.1 h.2
  · exact CompactLowByteBoundary04.windows j h.1 h.2
  · exact CompactLowByteBoundary05.windows j h.1 h.2
  · exact CompactLowByteBoundary06.windows j h.1 h.2
  · exact CompactLowByteBoundary07.windows j h.1 h.2
  · exact CompactLowByteBoundary08.windows j h.1 h.2
  · exact CompactLowByteBoundary09.windows j h.1 h.2
  · exact CompactLowByteBoundary10.windows j h.1 h.2
  · exact CompactLowByteBoundary11.windows j h.1 h.2
  · exact CompactLowByteBoundary12.windows j h.1 h.2

theorem all_windows (j : ℕ) (hj : j < bytes.length) :
    bytes.getD j 0 = (CompactSymbolicPorts.lowNat / 256^j) % 256 := by
  rw [bytes_length] at hj
  rw [bytes_getD j hj]
  exact point j hj

theorem decode_bytes : Nat.ofDigits 256 bytes = CompactSymbolicPorts.lowNat := by
  apply RadixWindowReconstruction.ofDigits_eq_of_windows 256 (by decide)
  · rw [bytes_length]
    exact CompactLowByteBound.low_lt_byte_power
  · exact all_windows

#print axioms CompactLowByteAssembly.point
#print axioms CompactLowByteAssembly.decode_bytes
end CompactLowByteAssembly
