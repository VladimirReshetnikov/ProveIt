import AbstractKernelMass
import KernelWeightMass
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ConcreteKernelMass2
open ConcreteSparseKernel KernelWeightMass
open scoped BigOperators
attribute [local irreducible] Compact943Data.rows

theorem kernel_total_mass :
    (kernelTerms.map Prod.snd).sum + 1 = CompactCoefficientMass.stencilMass := by
  have h := AbstractKernelMass.kernelShape_mass (fun i : Fin 943 => 4393-i.val)
    (fun i => 5495-i.val) selectorWeight (fun i : Fin 41 => 4393-CompactSymbolicKernel.position i)
    (fun i => 5495-CompactSymbolicKernel.position i) copyWeight
  change (kernelTerms.map Prod.snd).sum + 1 =
    2 * ((∑ i : Fin 943, selectorWeight i) + (∑ i : Fin 41, copyWeight i)) + 6 at h
  rw [selector_total, copy_total] at h
  exact h

#print axioms ConcreteKernelMass2.kernel_total_mass
end ConcreteKernelMass2
