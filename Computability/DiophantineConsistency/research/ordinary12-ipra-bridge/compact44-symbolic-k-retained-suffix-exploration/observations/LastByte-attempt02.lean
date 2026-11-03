import TopDigitClean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace LastByte
open ConcreteSparseKernel CompactSymbolicKernelOpaque SymbolicKernelBytes
attribute [local irreducible] paramKernel

theorem kernelDigits_get (i : ℕ) (hi : i < 8850) :
    PaddedRadixDigits.digit kernelDigits i = SparseRadix.coefficientAt kernelTerms i := by
  have hlen : i < kernelDigits.length := by
    simpa only [kernelDigits, List.length_map, List.length_range] using hi
  rw [PaddedRadixDigits.digit, List.getElem?_eq_getElem hlen]
  simp only [Option.getD_some, kernelDigits, List.getElem_map, List.getElem_range]

theorem zero_byte_of_gap (j : ℕ) (hlow : 5496 ≤ (8*j)/67)
    (hhigh : (8*j)/67+1 < 8849) :
    (paramKernel CompactSymbolicKernel.rho / 2 ^ (8*j)) % 256 = 0 := by
  rw [kernel_byte]
  have h1 : (8*j)/67 < 8849 := by omega
  have h2 : 5496 ≤ (8*j)/67+1 := by omega
  rw [kernelDigits_get ((8*j)/67) (by omega),
    kernelDigits_get ((8*j)/67+1) (by omega),
    TopDigit.coeff_gap _ hlow h1, TopDigit.coeff_gap _ h2 hhigh]
  simp

theorem zero_byte_range (j : ℕ) (hlo : 46029 ≤ j) (hhi : j < 74102) :
    (paramKernel CompactSymbolicKernel.rho / 2 ^ (8*j)) % 256 = 0 := by
  apply zero_byte_of_gap
  · omega
  · omega

theorem terminal_zero_byte (j : ℕ) (hlo : 74102 ≤ j) (hhi : j < 74110) :
    (paramKernel CompactSymbolicKernel.rho / 2 ^ (8*j)) % 256 = 0 := by
  interval_cases j <;>
    rw [kernel_byte] <;>
    norm_num only [Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod] <;>
    rw [kernelDigits_get 8848 (by decide), kernelDigits_get 8849 (by decide),
      TopDigit.coeff_gap 8848 (by decide) (by decide), TopDigit.coeff_top]

theorem last_byte : (paramKernel CompactSymbolicKernel.rho / 2 ^ (8 * 74110)) % 256 = 8 := by
  rw [kernel_byte]
  norm_num only [Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod]
  rw [kernelDigits_get 8848 (by decide), kernelDigits_get 8849 (by decide),
    TopDigit.coeff_gap 8848 (by decide) (by decide), TopDigit.coeff_top]
  norm_num

theorem zero_before_last (j : ℕ) (hlo : 46029 ≤ j) (hhi : j < 74110) :
    (paramKernel CompactSymbolicKernel.rho / 2 ^ (8*j)) % 256 = 0 := by
  by_cases h : j < 74102
  · exact zero_byte_range j hlo h
  · exact terminal_zero_byte j (by omega) hhi

theorem zero_after_last (j : ℕ) (hj : 74111 ≤ j) :
    (paramKernel CompactSymbolicKernel.rho / 2 ^ (8*j)) % 256 = 0 := by
  have he : 592884 ≤ 8*j := by omega
  have hpow : 2^592884 ≤ 2^(8*j) := Nat.pow_le_pow_right (by decide) he
  have hlt : paramKernel CompactSymbolicKernel.rho < 2^(8*j) :=
    lt_of_lt_of_le TopDigit.kernel_bounds.2 hpow
  rw [Nat.div_eq_of_lt hlt]

/-- Explicit zero-padded suffix, represented without materializing 28,081 zero bytes. -/
def suffixLiteral (i : ℕ) : ℕ := if i = 28081 then 8 else 0

theorem symbolic_suffix_literal (i : ℕ) :
    (paramKernel CompactSymbolicKernel.rho / 2 ^ (8*(46029+i))) % 256 = suffixLiteral i := by
  unfold suffixLiteral
  by_cases heq : i = 28081
  · subst i
    rw [show (46029 : ℕ) + 28081 = 74110 by decide]
    exact last_byte
  · simp only [heq, if_false]
    by_cases hlo : i < 28081
    · exact zero_before_last (46029+i) (by omega) (by omega)
    · exact zero_after_last (46029+i) (by omega)

#print axioms LastByte.symbolic_suffix_literal
#print axioms LastByte.zero_before_last
#print axioms LastByte.zero_after_last
#print axioms LastByte.terminal_zero_byte
#print axioms LastByte.zero_byte_range
#print axioms LastByte.kernelDigits_get
#print axioms LastByte.last_byte
end LastByte
