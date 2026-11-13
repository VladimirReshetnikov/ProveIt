import ConcreteSparseDigits
import DiophantineConsistency.CompactSelectorMassBridge
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SparseAggregateMass
open CompactSymbolicKernelOpaque ConcreteSparseKernel ConcreteSparsePositions
open scoped BigOperators
attribute [local irreducible] Compact943Data.rows

theorem coefficient_le_total (terms : List (ℕ × ℕ)) (j : ℕ) :
    SparseRadix.coefficientAt terms j ≤ (terms.map Prod.snd).sum := by
  induction terms with
  | nil => simp [SparseRadix.coefficientAt]
  | cons t ts ih =>
    by_cases h : t.1 = j
    · simp only [SparseRadix.coefficientAt, List.filter_cons, h, decide_true,
        List.map_cons, List.sum_cons, ↓reduceIte] at *
      omega
    · simp only [SparseRadix.coefficientAt, List.filter_cons, h, decide_false,
        ↓reduceIte, List.map_cons, List.sum_cons] at *
      omega

theorem kernel_total_mass :
    (kernelTerms.map Prod.snd).sum + 1 = CompactCoefficientMass.stencilMass := by
  simp only [kernelTerms, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, AbstractSparseFamily.twoBands, AbstractSparseFamily.terms,
    List.map_ofFn, List.sum_ofFn, Function.comp_def, selectorWeight, copyWeight]
  rw [CompactSelectorMassBridge.selector_fin_mass, CompactSelectorMassBridge.copy_fin_mass]
  unfold CompactCoefficientMass.stencilMass CompactCoefficientMass.coefficientMass
  omega

#print axioms SparseAggregateMass.coefficient_le_total
#print axioms SparseAggregateMass.kernel_total_mass
end SparseAggregateMass
