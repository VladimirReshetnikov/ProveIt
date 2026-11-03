import SymbolicKernelResidue

/-! Uncompiled attempt to prevent kernel expansion of the symbolic coefficient
while retaining an explicit equality to the actual parameterized kernel. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicKernelAlias
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicKernelResidue

@[irreducible] def kernelAlias : ℕ := paramKernel rho

theorem kernelAlias_eq : kernelAlias = paramKernel rho := by
  unfold kernelAlias
  rfl

theorem kernelAlias_mod : kernelAlias % 342946332593 = 284898815895 := by
  rw [kernelAlias_eq]
  exact symbolic_kernel_mod

#print axioms kernelAlias_eq
#print axioms kernelAlias_mod
end CompactSymbolicKernelAlias
