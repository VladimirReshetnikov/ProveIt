import DiophantineConsistency.Compact44.CompactKernelBlockSize
import DiophantineConsistency.ArithmeticModularCancellation

/-! Divisibility of the actual symbolic kernel by four. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
noncomputable section
namespace CompactKernelDivFour
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticStandardCasts ArithmeticWindowDigits
open CompactSymbolicKernel CompactSymbolicKernelOpaque ConcreteSparseKernel
attribute [local irreducible] paramKernel rho

theorem positive_positions : ∀ t ∈ kernelTerms, 0 < t.1 := by
  intro t ht
  simp only [kernelTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with (((rfl | rfl | rfl | rfl) | hs) | hc) | rfl
  all_goals try decide
  · simp only [AbstractSparseFamily.twoBands, AbstractSparseFamily.terms,
      List.mem_append, List.mem_ofFn] at hs
    rcases hs with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have hi := i.isLt; simp only; omega
    · have hi := i.isLt; simp only; omega
  · simp only [AbstractSparseFamily.twoBands, AbstractSparseFamily.terms,
      List.mem_append, List.mem_ofFn] at hc
    rcases hc with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have hi := position_lt_target i; simp only; omega
    · have hi := position_lt_target i; simp only; omega

theorem coefficient_zero : SparseRadix.coefficientAt kernelTerms 0 = 0 := by
  have hnone : kernelTerms.filter (fun t => t.1 = 0) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    exact Nat.ne_of_gt (positive_positions t ht)
  simp [SparseRadix.coefficientAt, hnone]

theorem kernel_mod_radix_generic (r : ℕ) (hr : 2^67 ≤ r) : paramKernel r % r = 0 := by
  have h := KernelDigitsBounded.kernel_digit r 0 hr (by decide)
  simpa only [pow_zero, Nat.div_one, coefficient_zero] using h

theorem kernel_dvd_four : 4 ∣ paramKernel rho := by
  have hr : 4 ∣ rho := by unfold rho; norm_num
  have hr0 : 2^67 ≤ rho := by unfold rho; exact le_rfl
  exact dvd_trans hr (Nat.dvd_of_mod_eq_zero (kernel_mod_radix_generic rho hr0))

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem kernel_model_dvd_four : (4:V) ∣ (paramKernel rho : V) := by
  have hn : paramKernel rho % 4 = 0 := Nat.mod_eq_zero_of_dvd kernel_dvd_four
  have h := cast_mod (V:=V) (paramKernel rho) 4
  rw [hn] at h
  apply mod_eq_zero_iff_dvd.mp
  simpa using h.symm

#print axioms CompactKernelDivFour.positive_positions
#print axioms CompactKernelDivFour.coefficient_zero
#print axioms CompactKernelDivFour.kernel_mod_radix_generic
#print axioms CompactKernelDivFour.kernel_dvd_four
#print axioms CompactKernelDivFour.kernel_model_dvd_four
end CompactKernelDivFour
