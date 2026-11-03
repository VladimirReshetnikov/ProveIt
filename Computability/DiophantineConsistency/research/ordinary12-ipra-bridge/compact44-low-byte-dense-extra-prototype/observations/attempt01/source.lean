import CompactLowByteDense

/-! Three further densely supported regions for the MC byte recipe. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowByteDenseExtra
open CompactLowByteWindow CompactLowByteDense

theorem support_digit (i : ℕ) (hhi : i < 1063) (hs : i ∈ CompactConcreteMask.support) :
    PaddedRadixDigits.digit lowDigits i = 2^67 - 2 := by
  rw [padded_digit, if_pos (by omega)]
  have hsp : i ≠ 1063 := by omega
  simp [CompactListMask.digit, hsp, hs]

def inDenseExtra (j : ℕ) : Prop :=
  (8233 ≤ j ∧ j < 8308) ∨ (8401 ≤ j ∧ j < 8468) ∨ (8484 ≤ j ∧ j < 8635)

theorem extra_dense_byte (j : ℕ) (hj : inDenseExtra j) :
    (CompactSymbolicPorts.lowNat / 2^(8*j)) % 256 = denseWindow ((8*j)%67) := by
  have hhi : (8*j)/67+1 < 1063 := by
    unfold inDenseExtra at hj
    omega
  have hs0 : (8*j)/67 ∈ CompactConcreteMask.support := by
    simp only [CompactConcreteMask.support, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_range, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    unfold inDenseExtra at hj
    omega
  have hs1 : (8*j)/67+1 ∈ CompactConcreteMask.support := by
    simp only [CompactConcreteMask.support, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_range, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    unfold inDenseExtra at hj
    omega
  rw [low_byte, support_digit _ (by omega) hs0, support_digit _ hhi hs1]
  exact dense_arithmetic _ (Nat.mod_lt _ (by decide))

#print axioms CompactLowByteDenseExtra.extra_dense_byte
end CompactLowByteDenseExtra
