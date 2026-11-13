import DiophantineConsistency.Compact44.ConcreteSparsePositions
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ConcreteSparseDigits
open CompactSymbolicKernelOpaque ConcreteSparseKernel ConcreteSparsePositions

theorem kernel_ofDigits (r : ℕ) :
    paramKernel r = Nat.ofDigits r ((List.range 8850).map (SparseRadix.coefficientAt kernelTerms)) := by
  rw [SparseRadix.ofDigits_map_range, SparseRadix.sparse_sum r 8850 kernelTerms kernel_positions_bounded]
  exact kernel_weighted_sum r

theorem kernel_digit (r i : ℕ) (hr : 0 < r)
    (hcoeff : ∀ j < 8850, SparseRadix.coefficientAt kernelTerms j < r) (hi : i < 8850) :
    (paramKernel r / r ^ i) % r = SparseRadix.coefficientAt kernelTerms i := by
  rw [kernel_weighted_sum r]
  exact SparseRadix.sparse_terms_digit r 8850 i kernelTerms hr kernel_positions_bounded hcoeff hi

theorem kernel_lt (r : ℕ) (hr : 1 < r)
    (hcoeff : ∀ j < 8850, SparseRadix.coefficientAt kernelTerms j < r) :
    paramKernel r < r ^ 8850 := by
  have h := SparseRadix.finite_sum_lt r 8850 (SparseRadix.coefficientAt kernelTerms) hr hcoeff
  rw [SparseRadix.sparse_sum r 8850 kernelTerms kernel_positions_bounded, ← kernel_weighted_sum r] at h
  exact h

#print axioms ConcreteSparseDigits.kernel_ofDigits
#print axioms ConcreteSparseDigits.kernel_digit
#print axioms ConcreteSparseDigits.kernel_lt
end ConcreteSparseDigits
