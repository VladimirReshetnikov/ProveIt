import DiophantineConsistency.Sign17KDigitBoundAssembly

/-! SOURCE ONLY. Proposed canonical digits of the symbolic K. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KCanonicalDigits
open CurrentKernel2011

theorem last_digit_is_one
    (h : Sign17KRadixStream.digits Sign17KLiteralCoefficients.literal ≠ []) :
    (Sign17KRadixStream.digits Sign17KLiteralCoefficients.literal).getLast h = 1 := by
  have hs : Sign17KRadixStream.digits Sign17KLiteralCoefficients.literal =
      ((Sign17KRadixStream.lowPrefix ++
        Sign17KRadixStream.block Sign17KLiteralCoefficients.literal) ++
          List.replicate 1014 0) ++ [1] := by
    simp only [Sign17KRadixStream.digits, Sign17KRadixStream.suffix, List.append_assoc]
  simp only [hs, List.getLast_append_of_ne_nil, List.getLast_singleton]

theorem canonical_digits :
    Nat.digits radix K = Sign17KRadixStream.digits Sign17KLiteralCoefficients.literal := by
  rw [← Sign17KRadixStreamCurrent.current_K_stream]
  apply Nat.digits_ofDigits
  · decide +kernel
  · exact Sign17KDigitBoundAssembly.actual_digits_bound
  · intro h
    rw [last_digit_is_one h]
    decide

end DiophantineConsistency.Sign17KCanonicalDigits
#print axioms DiophantineConsistency.Sign17KCanonicalDigits.canonical_digits
