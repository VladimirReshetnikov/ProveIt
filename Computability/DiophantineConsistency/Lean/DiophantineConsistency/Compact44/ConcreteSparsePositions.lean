import DiophantineConsistency.Compact44.ConcreteSparseKernel
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ConcreteSparsePositions
open CompactSymbolicKernel CompactKernelFiniteCert ForeignBandGeometry ConcreteSparseKernel

theorem twoBands_bounded {n : ℕ} (bound : ℕ) (left right weight : Fin n → ℕ)
    (hleft : ∀ i, left i < bound) (hright : ∀ i, right i < bound) :
    ∀ t ∈ AbstractSparseFamily.twoBands left right weight, t.1 < bound := by
  intro t ht
  simp only [AbstractSparseFamily.twoBands, AbstractSparseFamily.terms,
    List.mem_append, List.mem_ofFn] at ht
  rcases ht with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact hleft i
  · exact hright i

theorem selector_positions_bounded :
    ∀ t ∈ AbstractSparseFamily.twoBands (fun i : Fin 943 => 4393-i.val)
      (fun i => 5495-i.val) selectorWeight, t.1 < 8850 := by
  apply twoBands_bounded
  · intro i
    have h := reflected_range i.val (selector_allowed i)
    omega
  · intro i
    have h := reflected_range i.val (selector_allowed i)
    omega

theorem copy_positions_bounded :
    ∀ t ∈ AbstractSparseFamily.twoBands (fun i : Fin 41 => 4393-position i)
      (fun i => 5495-position i) copyWeight, t.1 < 8850 := by
  apply twoBands_bounded
  · intro i
    have h := reflected_range (position i) (copy_allowed i)
    omega
  · intro i
    have h := reflected_range (position i) (copy_allowed i)
    omega

theorem kernel_positions_bounded : ∀ t ∈ kernelTerms, t.1 < 8850 := by
  intro t ht
  simp only [kernelTerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with (((rfl | rfl | rfl | rfl) | hs) | hc) | rfl
  all_goals try decide
  · exact selector_positions_bounded t hs
  · exact copy_positions_bounded t hc

#print axioms ConcreteSparsePositions.twoBands_bounded
#print axioms ConcreteSparsePositions.selector_positions_bounded
#print axioms ConcreteSparsePositions.copy_positions_bounded
#print axioms ConcreteSparsePositions.kernel_positions_bounded
end ConcreteSparsePositions
