import ConcreteSparseKernel
import SparseFamilyMass
import DiophantineConsistency.CompactSelectorMassBridge
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ConcreteKernelMass
open ConcreteSparseKernel
open scoped BigOperators
attribute [local irreducible] Compact943Data.rows

theorem selector_total : (∑ i : Fin 943, selectorWeight i) = CompactCoefficientMass.selectorMass := by
  exact CompactSelectorMassBridge.selector_fin_mass

theorem copy_total : (∑ i : Fin 41, copyWeight i) = CompactCoefficientMass.copyMass := by
  exact CompactSelectorMassBridge.copy_fin_mass

theorem kernel_total_mass :
    (kernelTerms.map Prod.snd).sum + 1 = CompactCoefficientMass.stencilMass := by
  simp only [kernelTerms, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Prod.snd, SparseFamilyMass.twoBands_total]
  rw [selector_total, copy_total]
  unfold CompactCoefficientMass.stencilMass CompactCoefficientMass.coefficientMass
  omega

#print axioms ConcreteKernelMass.selector_total
#print axioms ConcreteKernelMass.copy_total
#print axioms ConcreteKernelMass.kernel_total_mass
end ConcreteKernelMass
