import DiophantineConsistency.Sign17KRadixStream
import DiophantineConsistency.Sign17KLiteralCoefficients

/-! SOURCE ONLY. Proposed in-Lean literal radix stream specialization for K. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KRadixStreamCurrent
open CurrentKernel2011

theorem current_K_stream :
    Nat.ofDigits radix
      (Sign17KRadixStream.digits Sign17KLiteralCoefficients.literal) = K := by
  rw [Sign17KRadixStream.digit_value]
  exact Sign17KLiteralCoefficients.K_literal.symm

end DiophantineConsistency.Sign17KRadixStreamCurrent
#print axioms DiophantineConsistency.Sign17KRadixStreamCurrent.current_K_stream
