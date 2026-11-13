import ConcreteSparseDigits
import KernelCoefficientBound
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace KernelDigitsBounded
open CompactSymbolicKernelOpaque ConcreteSparseKernel

theorem kernel_digit (r i : ℕ) (hr : 2^67 ≤ r) (hi : i < 8850) :
    (paramKernel r / r ^ i) % r = SparseRadix.coefficientAt kernelTerms i := by
  have hp : 0 < r := by have : 0 < 2^67 := by norm_num; omega
  exact ConcreteSparseDigits.kernel_digit r i hp
    (fun j _ => KernelCoefficientBound.kernel_coefficient_bound r j hr) hi

theorem kernel_lt (r : ℕ) (hr : 2^67 ≤ r) : paramKernel r < r ^ 8850 := by
  have hp : 1 < r := by have : 1 < 2^67 := by norm_num; omega
  exact ConcreteSparseDigits.kernel_lt r hp
    (fun j _ => KernelCoefficientBound.kernel_coefficient_bound r j hr)

theorem rho_digit (i : ℕ) (hi : i < 8850) :
    (paramKernel CompactSymbolicKernel.rho / CompactSymbolicKernel.rho ^ i) %
      CompactSymbolicKernel.rho = SparseRadix.coefficientAt kernelTerms i := by
  apply kernel_digit
  · exact le_rfl
  · exact hi

#print axioms KernelDigitsBounded.kernel_digit
#print axioms KernelDigitsBounded.kernel_lt
#print axioms KernelDigitsBounded.rho_digit
end KernelDigitsBounded
