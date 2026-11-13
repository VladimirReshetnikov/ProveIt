import ConcreteSparsePositions
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace KernelTermBounds
open CompactSymbolicKernel ConcreteSparseKernel
attribute [local irreducible] Compact943Data.rows

theorem selector_weight_bound (i : Fin 943) : selectorWeight i ≤ 2^51 + 1 := by
  unfold selectorWeight CompactCoefficientMass.selector
  have hm := Nat.mul_le_mul_left (2^10) (Nat.sub_le (2^41) (CompactCoefficientMass.value (Compact943Data.row i)))
  have hn : 2^10 * 2^41 = 2^51 := by norm_num
  omega

theorem copy_weight_bound (i : Fin 41) : copyWeight i ≤ 2^51 + 1 := by
  unfold copyWeight
  have hi : 10 + i.val ≤ 51 := by have := i.isLt; omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hi
  exact le_trans hp (Nat.le_succ _)

theorem twoBands_weights {n : ℕ} (left right weight : Fin n → ℕ) (B : ℕ)
    (h : ∀ i, weight i ≤ B) :
    ∀ t ∈ AbstractSparseFamily.twoBands left right weight, t.2 ≤ B := by
  intro t ht
  simp only [AbstractSparseFamily.twoBands, AbstractSparseFamily.terms,
    List.mem_append, List.mem_ofFn] at ht
  rcases ht with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> exact h i

theorem kernel_weights_bound : ∀ t ∈ kernelTerms, t.2 ≤ 2^51 + 1 := by
  intro t ht
  simp only [kernelTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with (((rfl | rfl | rfl | rfl) | hs) | hc) | rfl
  all_goals try decide
  · exact twoBands_weights _ _ _ _ selector_weight_bound t hs
  · exact twoBands_weights _ _ _ _ copy_weight_bound t hc

theorem kernel_terms_length : kernelTerms.length = 1973 := by
  simp [kernelTerms, AbstractSparseFamily.twoBands, AbstractSparseFamily.terms]

#print axioms KernelTermBounds.selector_weight_bound
#print axioms KernelTermBounds.copy_weight_bound
#print axioms KernelTermBounds.twoBands_weights
#print axioms KernelTermBounds.kernel_weights_bound
#print axioms KernelTermBounds.kernel_terms_length
end KernelTermBounds
