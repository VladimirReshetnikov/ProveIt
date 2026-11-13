import CompactLowByteRecipeData
import CompactLowByteWindow

/-! Finite symbolic byte-window certificate for [8225,8233). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowByteBoundary03

theorem windows (j : ℕ) (hlo : 8225 ≤ j) (hhi : j < 8233) :
    CompactLowByteRecipeData.byteAt j = (CompactSymbolicPorts.lowNat / 256^j) % 256 := by
  have hp : (256:ℕ)^j = 2^(8*j) := by
    rw [show (256:ℕ) = 2^8 by norm_num, ← pow_mul]
  rw [hp, CompactLowByteWindow.low_byte]
  interval_cases j <;>
    norm_num [CompactLowByteRecipeData.byteAt, CompactLowByteRecipeData.denseIndex,
      CompactLowByteRecipeData.irregularByte, CompactLowByteWindow.padded_digit,
      CompactListMask.digit, CompactConcreteMask.support]

#print axioms CompactLowByteBoundary03.windows
end CompactLowByteBoundary03
