import DiophantineConsistency.CurrentEarlyPadding2011

namespace DiophantineConsistency.CurrentEarlyPadding2011Checks

open CurrentEarlyPadding2011 CurrentReflectedGeometry2011 CurrentKernel2011
  WangTiles942 PaddingStaircase
open scoped BigOperators

set_option Elab.async false

-- The first checked prefix has precisely one source, not an empty prefix
-- or an extra endpoint. This remains symbolic in the source values.
example (a : ℕ → ℕ) :
    (∑ p ∈ Finset.range 942, if 942 ≤ 1 + p then a (1 + p - 942) else 0) = a 0 := by
  rw [shifted_suffix_sum a (by decide : 1 ≤ 942)]
  simp only [prefixSum, Finset.sum_range_one]

-- At the last test the actual cutoff tile866 supplies source0.
example : source 546 (.inl (866 : Fin 942)) = 0 := by
  rw [source, position, CurrentSelectorTail2011.cutoff_position]

-- The other endpoint is physical coefficient941, which supplies source482.
example : source 546 (.inl (physicalEquiv.symm (941 : Fin 942))) = 482 := by
  have hp := congrArg Fin.val (physicalEquiv.apply_symm_apply (941 : Fin 942))
  change physicalPosition (physicalEquiv.symm (941 : Fin 942)) = 941 at hp
  rw [source, position, hp]

-- The spatial input genuinely comes from the preceding cell. It is retained
-- in paddingUnit, whereas the marker input has unsupported residue1071.
example : ((0 : ZMod (2 * 2011)) + 64 - 2020).val = 2066 ∧
    ((0 : ZMod (2 * 2011)) + 64 - 2020).val % 2011 = 55 ∧
    ((0 : ZMod (2 * 2011)) + 64 - 1004).val % 2011 = 1071 := by decide

-- Both ends are actual full-mask bit3 tests in a later cell too.
example : CurrentHighDigits2011.maskDigits (N := 2) (2011 + 64) = 8 :=
  padding_mask 2011 (by decide) (j := 1) (by decide)

example : CurrentHighDigits2011.maskDigits (N := 2) (2011 + 546) = 8 :=
  padding_mask 2011 (by decide) (j := 483) (by decide)

-- Both ends of the relevant phase range satisfy the exact premises.
example : (2 ^ 7 : ℕ) % 16 = 0 ∧ (2 ^ 10 : ℕ) % 16 = 0 ∧
    137820284543942 + 2 ^ 10 + 60 < CurrentMasks2011.radix := by decide

#print axioms shifted_suffix_sum
#print axioms early_reflected_bound
#print axioms early_carry_zero
#print axioms selector_sources_eq_prefix
#print axioms reflected_padding_residue
#print axioms padding_convolution
#print axioms padding_incoming_zero
#print axioms padding_digit_residue
#print axioms padding_mask
#print axioms padding_bindings

end DiophantineConsistency.CurrentEarlyPadding2011Checks
