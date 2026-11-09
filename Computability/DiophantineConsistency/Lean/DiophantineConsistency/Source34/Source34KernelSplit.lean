import DiophantineConsistency.Source34.Source34SparseKernel
import DiophantineConsistency.Mixed121.Mixed121KernelSplit
import DiophantineConsistency.ArithmeticStandardCasts

/-! # The source34 kernel: isolated top digit, lower mass, divisibility by four

`Mixed121KernelSplit` at the source34 tuple, with the theorem names kept.

* `kernel_split_generic`: `paramKernel r = r^8802 + lowerKernelAt r`, where the
  lower part collects the 1978 terms with exponent below `5496`
  (121x8801: the top term was `r^8843`);
* `lower_lt`, `lower_le`: `lowerKernelAt ρ < ρ^5496` and
  `lowerKernelAt r ≤ 2^110·r^5495`;
* `kernel_mod_radix_generic`, `kernel_dvd_four`: every exponent is positive,
  so `r ∣ paramKernel r` for `r ≥ 2^121`, and `4 ∣ K`.

`Mixed121KernelSplit.weighted_bound` is generic and used directly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34KernelSplit
open Mixed121Kernel (rho)
open Source34Kernel Source34KernelFiniteCert Source34SparseKernel
open scoped BigOperators
attribute [local irreducible] paramKernel rho

/-- All terms below the isolated top radix digit, without expansion. -/
def lowerKernelAt (r : ℕ) : ℕ := (lowTerms.map (fun t => t.2 * r ^ t.1)).sum

theorem coeff_low_eq (j : ℕ) (hj : j < 5496) :
    SparseRadix.coefficientAt lowTerms j = SparseRadix.coefficientAt kernelTerms j := by
  rw [kernelTerms_split]
  simp [SparseRadix.coefficientAt, show (8802 : ℕ) ≠ j by omega]

theorem lower_lt : lowerKernelAt rho < rho ^ 5496 := by
  have hr : 2^121 ≤ rho := by unfold rho; exact le_rfl
  unfold lowerKernelAt
  rw [← SparseRadix.sparse_sum rho 5496 lowTerms lowTerms_lt]
  apply SparseRadix.finite_sum_lt
  · exact lt_of_lt_of_le (by norm_num) hr
  · intro j hj
    rw [coeff_low_eq j hj]
    exact kernel_coefficient_bound rho j hr

theorem kernel_split_generic (r : ℕ) : paramKernel r = r ^ 8802 + lowerKernelAt r := by
  rw [kernel_weighted_sum, kernelTerms_split]
  unfold lowerKernelAt
  rw [List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero]
  exact Nat.add_comm _ _

theorem low_length : lowTerms.length ≤ 1979 := by
  have hl := kernel_terms_length
  rw [kernelTerms_split] at hl
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  omega

/-- The lower coefficient mass is at most `2^110`, without expanding the row table. -/
theorem lower_le (r : ℕ) (hr : 1 ≤ r) : lowerKernelAt r ≤ 2^110 * r^5495 := by
  unfold lowerKernelAt
  have hp : ∀ t ∈ lowTerms, t.1 ≤ 5495 := by
    intro t ht
    have hh := lowTerms_lt t ht
    omega
  have hw : ∀ t ∈ lowTerms, t.2 ≤ 2^99 := by
    intro t ht
    apply kernel_weights_bound t
    rw [kernelTerms_split]
    exact List.mem_append_left _ ht
  have h := Mixed121KernelSplit.weighted_bound r 5495 (2^99) hr lowTerms hp hw
  calc
    _ ≤ lowTerms.length * (2^99 * r^5495) := h
    _ ≤ 1979 * (2^99 * r^5495) := Nat.mul_le_mul_right _ low_length
    _ = (1979 * 2^99) * r^5495 := by ring
    _ ≤ 2^110 * r^5495 := Nat.mul_le_mul_right _ (by norm_num)

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
    · have hi := reflected_range (extraPos i) (extra_allowed i); simp only; omega
    · have hi := reflected_range (extraPos i) (extra_allowed i); simp only; omega

theorem coefficient_zero : SparseRadix.coefficientAt kernelTerms 0 = 0 := by
  have hnone : kernelTerms.filter (fun t => t.1 = 0) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    exact Nat.ne_of_gt (positive_positions t ht)
  simp [SparseRadix.coefficientAt, hnone]

theorem kernel_mod_radix_generic (r : ℕ) (hr : 2^121 ≤ r) : paramKernel r % r = 0 := by
  have h := kernel_digit r 0 hr (by decide)
  simpa only [pow_zero, Nat.div_one, coefficient_zero] using h

theorem kernel_dvd_four : 4 ∣ paramKernel rho := by
  have hr : 4 ∣ rho := by unfold rho; norm_num
  have hr0 : 2^121 ≤ rho := by unfold rho; exact le_rfl
  exact dvd_trans hr (Nat.dvd_of_mod_eq_zero (kernel_mod_radix_generic rho hr0))

open LO LO.FirstOrder LO.FirstOrder.Arithmetic in
theorem kernel_model_dvd_four {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (4:V) ∣ (paramKernel rho : V) := by
  have hn : paramKernel rho % 4 = 0 := Nat.mod_eq_zero_of_dvd kernel_dvd_four
  have h := DiophantineConsistency.ArithmeticStandardCasts.cast_mod (V:=V) (paramKernel rho) 4
  rw [hn] at h
  apply mod_eq_zero_iff_dvd.mp
  simpa using h.symm

#print axioms Source34KernelSplit.lower_lt
#print axioms Source34KernelSplit.kernel_split_generic
#print axioms Source34KernelSplit.lower_le
#print axioms Source34KernelSplit.kernel_dvd_four
#print axioms Source34KernelSplit.kernel_model_dvd_four
end Source34KernelSplit
