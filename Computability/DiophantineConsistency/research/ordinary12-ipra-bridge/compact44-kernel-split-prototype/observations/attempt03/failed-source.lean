import TopDigitClean

/-! Split the exact symbolic kernel at its isolated top radix digit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactKernelSplit
open CompactSymbolicKernel CompactSymbolicKernelOpaque ConcreteSparseKernel TopDigit
open scoped BigOperators
attribute [local irreducible] paramKernel rho

/-- All terms below the isolated top radix digit, without expansion. -/
def lowerKernel : ℕ := (lowTerms.map (fun t => t.2 * rho ^ t.1)).sum

theorem coeff_low_eq (j : ℕ) (hj : j < 5496) :
    SparseRadix.coefficientAt lowTerms j = SparseRadix.coefficientAt kernelTerms j := by
  have hk : kernelTerms = lowTerms ++ [(8849,1)] := by rfl
  rw [hk]
  simp [SparseRadix.coefficientAt, show (8849 : ℕ) ≠ j by omega]

theorem lower_lt : lowerKernel < rho ^ 5496 := by
  have hr : 2^67 ≤ rho := by unfold rho; exact le_rfl
  unfold lowerKernel
  rw [← SparseRadix.sparse_sum rho 5496 lowTerms lowTerms_lt]
  apply SparseRadix.finite_sum_lt
  · exact lt_of_lt_of_le (by norm_num) hr
  · intro j hj
    rw [coeff_low_eq j hj]
    exact KernelCoefficientBound.kernel_coefficient_bound rho j hr

theorem kernel_split : paramKernel rho = rho ^ 8849 + lowerKernel := by
  rw [kernel_weighted_sum]
  have hk : kernelTerms = lowTerms ++ [(8849,1)] := by rfl
  rw [hk]
  unfold lowerKernel
  rw [List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero]
  exact Nat.add_comm _ _

#print axioms CompactKernelSplit.coeff_low_eq
#print axioms CompactKernelSplit.lower_lt
#print axioms CompactKernelSplit.kernel_split
end CompactKernelSplit
