import DiophantineConsistency.Compact44.CompactLowByteRecipeData
import DiophantineConsistency.Compact44.CompactLowByteWindow

/-! Finite symbolic byte-window certificate for [18375,18392). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowByteBoundary10

theorem windows (j : ℕ) (hlo : 18375 ≤ j) (hhi : j < 18392) :
    CompactLowByteRecipeData.byteAt j = (CompactSymbolicPorts.lowNat / 256^j) % 256 := by
  have hp : (256:ℕ)^j = 2^(8*j) := by
    rw [show (256:ℕ) = 2^8 by norm_num, ← pow_mul]
  rw [hp, CompactLowByteWindow.low_byte]
  interval_cases j <;>
    norm_num [CompactLowByteRecipeData.byteAt, CompactLowByteRecipeData.denseIndex,
      CompactLowByteRecipeData.irregularByte, CompactLowByteWindow.padded_digit,
      CompactListMask.digit, CompactConcreteMask.support]

#print axioms CompactLowByteBoundary10.windows
end CompactLowByteBoundary10
