import ConcreteSparseKernel
import DiophantineConsistency.CompactSelectorMassBridge
set_option autoImplicit false
set_option Elab.async false
namespace KernelWeightMass
open ConcreteSparseKernel
open scoped BigOperators
attribute [local irreducible] Compact943Data.rows

theorem selector_total : (∑ i : Fin 943, selectorWeight i) = CompactCoefficientMass.selectorMass := by
  exact CompactSelectorMassBridge.selector_fin_mass

theorem copy_total : (∑ i : Fin 41, copyWeight i) = CompactCoefficientMass.copyMass := by
  exact CompactSelectorMassBridge.copy_fin_mass

#print axioms KernelWeightMass.selector_total
#print axioms KernelWeightMass.copy_total
end KernelWeightMass
