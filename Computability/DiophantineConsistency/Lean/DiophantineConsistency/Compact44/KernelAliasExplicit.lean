import DiophantineConsistency.Compact44.SymbolicKernelResidue

/-! Uncompiled alternative using explicit equality transport rather than rw. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactSymbolicKernelAliasExplicit
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicKernelResidue
attribute [local irreducible] paramKernel rho

@[irreducible] def kernelAlias : ℕ := paramKernel rho

theorem kernelAlias_eq : kernelAlias = paramKernel rho := by
  unfold kernelAlias
  rfl

theorem kernelAlias_mod : kernelAlias % Modulus = 284898815895 :=
  (congrArg (fun k : ℕ => k % Modulus = 284898815895) kernelAlias_eq).mpr
    symbolic_kernel_mod

#print axioms kernelAlias_eq
#print axioms kernelAlias_mod
end CompactSymbolicKernelAliasExplicit
