import DiophantineConsistency.Compact44.ByteWindow
import DiophantineConsistency.Compact44.ConcreteSparseDigits
import DiophantineConsistency.Compact44.KernelCoefficientBound
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymbolicKernelBytes
open ConcreteSparseKernel CompactSymbolicKernelOpaque

def kernelDigits : List ℕ :=
  (List.range 8850).map (SparseRadix.coefficientAt kernelTerms)

theorem kernelDigits_bounded : ∀ x ∈ kernelDigits, x < 2^67 := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact KernelCoefficientBound.kernel_coefficient_bound (2^67) i le_rfl

theorem kernel_byte (j : ℕ) :
    (paramKernel CompactSymbolicKernel.rho / 2^(8*j)) % 256 =
      (PaddedRadixDigits.digit kernelDigits ((8*j)/67) / 2^((8*j)%67) +
       PaddedRadixDigits.digit kernelDigits ((8*j)/67+1) * 2^(67-(8*j)%67)) % 256 := by
  have h := ByteWindow.byte kernelDigits kernelDigits_bounded j
  have hk : paramKernel CompactSymbolicKernel.rho = Nat.ofDigits (2^67) kernelDigits := by
    exact ConcreteSparseDigits.kernel_ofDigits CompactSymbolicKernel.rho
  rw [← hk] at h
  exact h

#print axioms SymbolicKernelBytes.kernelDigits_bounded
#print axioms SymbolicKernelBytes.kernel_byte
end SymbolicKernelBytes
