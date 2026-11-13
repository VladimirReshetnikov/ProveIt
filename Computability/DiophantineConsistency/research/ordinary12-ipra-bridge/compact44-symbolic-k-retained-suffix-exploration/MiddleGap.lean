import LastByte
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace MiddleGap
open ConcreteSparseKernel CompactSymbolicKernelOpaque SymbolicKernelBytes
attribute [local irreducible] paramKernel

theorem term_avoids (j : ℕ) (hj : 2202 ≤ j) (hj' : j < 3298) :
    ∀ t ∈ kernelTerms, t.1 ≠ j := by
  intro t ht
  simp only [kernelTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    AbstractSparseFamily.twoBands, AbstractSparseFamily.terms, List.mem_ofFn] at ht
  rcases ht with (((rfl | rfl | rfl | rfl) | (⟨i, rfl⟩ | ⟨i, rfl⟩)) |
      (⟨i, rfl⟩ | ⟨i, rfl⟩)) | rfl
  all_goals try omega
  all_goals
    have h := ForeignBandGeometry.copy_allowed i
    unfold ForeignBandGeometry.Allowed at h
    omega

theorem coeff_middle_gap (j : ℕ) (hj : 2202 ≤ j) (hj' : j < 3298) :
    SparseRadix.coefficientAt kernelTerms j = 0 := by
  have hnone : kernelTerms.filter (fun t => t.1 = j) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    exact term_avoids j hj hj' t ht
  simp only [SparseRadix.coefficientAt, hnone, List.map_nil, List.sum_nil]

theorem zero_byte_range (j : ℕ) (hlo : 18442 ≤ j) (hhi : j < 27613) :
    (paramKernel CompactSymbolicKernel.rho / 2 ^ (8*j)) % 256 = 0 := by
  rw [kernel_byte]
  have h1 : 2202 ≤ (8*j)/67 := by omega
  have h2 : (8*j)/67+1 < 3298 := by omega
  rw [LastByte.kernelDigits_get ((8*j)/67) (by omega),
    LastByte.kernelDigits_get ((8*j)/67+1) (by omega),
    coeff_middle_gap _ h1 (by omega), coeff_middle_gap _ (by omega) h2]
  simp

#print axioms MiddleGap.term_avoids
#print axioms MiddleGap.coeff_middle_gap
#print axioms MiddleGap.zero_byte_range
end MiddleGap
