import DiophantineConsistency.CompactSymbolicKernelOpaque
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicKernelLink
open LO LO.FirstOrder LO.FirstOrder.Arithmetic CompactSymbolicKernel CompactSymbolicKernelOpaque
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
attribute [local irreducible] rho

theorem kernel_eq_param : kernelNat = paramKernel rho := by
  simp only [kernelNat, bareTerms, selectorTerms, copyTerms, reflected, block, paramKernel]
#print axioms CompactSymbolicKernelLink.kernel_eq_param
end CompactSymbolicKernelLink
