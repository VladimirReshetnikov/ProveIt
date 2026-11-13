import DiophantineConsistency.Sign17KBytePatterns00

/-! SOURCE ONLY. Generic radix/byte block alignment. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KByteAlignmentCore

def aligned (digits bytes : List ℕ) : Prop :=
  digits.length = 8 ∧ bytes.length = 47 ∧
    Nat.ofDigits CurrentKernel2011.radix digits = Nat.ofDigits 256 bytes

end DiophantineConsistency.Sign17KByteAlignmentCore
