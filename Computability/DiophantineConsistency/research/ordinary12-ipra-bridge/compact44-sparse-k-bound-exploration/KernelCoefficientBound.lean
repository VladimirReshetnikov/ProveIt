import SparseCountBound
import KernelTermBounds
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace KernelCoefficientBound
open ConcreteSparseKernel KernelTermBounds

theorem kernel_coefficient_bound (r j : ℕ) (hr : 2^67 ≤ r) :
    SparseRadix.coefficientAt kernelTerms j < r := by
  have h := SparseCountBound.coefficient_le_length_mul kernelTerms j (2^51 + 1) kernel_weights_bound
  rw [kernel_terms_length] at h
  have hsmall : 1973 * (2^51 + 1) < 2^67 := by norm_num
  omega

#print axioms KernelCoefficientBound.kernel_coefficient_bound
end KernelCoefficientBound
