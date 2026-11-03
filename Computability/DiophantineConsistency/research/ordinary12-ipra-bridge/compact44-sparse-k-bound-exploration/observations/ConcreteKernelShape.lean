import AbstractKernelMass
import ConcreteSparseKernel
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace ConcreteKernelShape
open ConcreteSparseKernel
open scoped BigOperators
attribute [local irreducible] Compact943Data.rows selectorWeight copyWeight

theorem kernel_total_abstract :
    (kernelTerms.map Prod.snd).sum + 1 =
      2 * ((∑ i : Fin 943, selectorWeight i) + (∑ i : Fin 41, copyWeight i)) + 6 := by
  exact AbstractKernelMass.kernelShape_mass (fun i : Fin 943 => 4393-i.val)
    (fun i => 5495-i.val) selectorWeight (fun i : Fin 41 => 4393-CompactSymbolicKernel.position i)
    (fun i => 5495-CompactSymbolicKernel.position i) copyWeight

#print axioms ConcreteKernelShape.kernel_total_abstract
end ConcreteKernelShape
