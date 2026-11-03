import CompactLowByteWindow

/-! An initial finite symbolic-MC byte window certificate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLowBytePrefix

def prefix : List ℕ := 254 :: List.replicate 15 255

theorem prefix_windows (j : ℕ) (hj : j < 16) :
    prefix.getD j 0 = (CompactSymbolicPorts.lowNat / 256^j) % 256 := by
  have hp : (256:ℕ)^j = 2^(8*j) := by
    rw [show (256:ℕ) = 2^8 by norm_num, ← pow_mul]
  rw [hp, CompactLowByteWindow.low_byte]
  interval_cases j <;>
    norm_num [prefix, CompactLowByteWindow.padded_digit,
      CompactListMask.digit, CompactConcreteMask.support]

#print axioms CompactLowBytePrefix.prefix_windows
end CompactLowBytePrefix
