import DiophantineConsistency.Compact44.SymbolicKernelBytes
import DiophantineConsistency.Compact44.TopDigitClean
import DiophantineConsistency.Compact44.RadixWindowReconstruction
import Mathlib.Data.List.GetD

/-! Closed local-window bytes for the symbolic compact kernel coefficient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactKernelByteRecipe
open SymbolicKernelBytes CompactSymbolicKernelOpaque
attribute [local irreducible] paramKernel CompactSymbolicKernel.rho kernelDigits

def byteAt (j : ℕ) : ℕ :=
  (PaddedRadixDigits.digit kernelDigits ((8*j)/67) / 2^((8*j)%67) +
   PaddedRadixDigits.digit kernelDigits ((8*j)/67+1) * 2^(67-(8*j)%67)) % 256

theorem byteAt_eq (j : ℕ) : byteAt j =
    (paramKernel CompactSymbolicKernel.rho / 256^j) % 256 := by
  have hp : (256:ℕ)^j = 2^(8*j) := by
    rw [show (256:ℕ) = 2^8 by norm_num, ← pow_mul]
  rw [hp]
  exact (kernel_byte j).symm

def bytes : List ℕ := (List.range 74111).map byteAt
attribute [local irreducible] bytes

theorem bytes_length : bytes.length = 74111 := by simp [bytes]

theorem bytes_getD (j : ℕ) (hj : j < 74111) : bytes.getD j 0 = byteAt j := by
  unfold bytes
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_range]

theorem kernel_lt_byte_power :
    paramKernel CompactSymbolicKernel.rho < 256^74111 := by
  calc
    paramKernel CompactSymbolicKernel.rho < 2^592884 := TopDigit.kernel_bounds.2
    _ < 2^(8*74111) := by
      apply Nat.pow_lt_pow_right (a := 2)
      · omega
      · omega
    _ = 256^74111 := by
      rw [pow_mul, show (2:ℕ)^8 = 256 by norm_num]

theorem bytes_windows (j : ℕ) (hj : j < bytes.length) : bytes.getD j 0 =
    (paramKernel CompactSymbolicKernel.rho / 256^j) % 256 := by
  rw [bytes_length] at hj
  rw [bytes_getD j hj]
  exact byteAt_eq j

theorem decode_bytes : Nat.ofDigits 256 bytes = paramKernel CompactSymbolicKernel.rho := by
  apply RadixWindowReconstruction.ofDigits_eq_of_windows 256 (by decide)
  · rw [bytes_length]
    exact kernel_lt_byte_power
  · exact bytes_windows

#print axioms CompactKernelByteRecipe.byteAt_eq
#print axioms CompactKernelByteRecipe.kernel_lt_byte_power
#print axioms CompactKernelByteRecipe.decode_bytes
end CompactKernelByteRecipe
