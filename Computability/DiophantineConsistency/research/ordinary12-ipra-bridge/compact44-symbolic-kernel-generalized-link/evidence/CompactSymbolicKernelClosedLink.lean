import DiophantineConsistency.CompactSymbolicKernelOldShape
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicKernelClosedLink
open CompactSymbolicKernel CompactSymbolicKernelOldShape
open scoped BigOperators
attribute [local irreducible] rho

theorem kernel_eq_oldAt : kernelNat = oldAt rho := by
  change bareTerms + selectorTerms + copyTerms + block * rho^42 = oldAt rho
  unfold bareTerms selectorTerms copyTerms reflected block oldAt bareAt selectorAt copyAt reflectedAt
  generalize h : rho = r
  rfl
#print axioms CompactSymbolicKernelClosedLink.kernel_eq_oldAt
end CompactSymbolicKernelClosedLink
