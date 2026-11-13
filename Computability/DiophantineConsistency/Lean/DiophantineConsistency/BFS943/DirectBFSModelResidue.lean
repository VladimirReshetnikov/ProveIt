import DiophantineConsistency.BFS943.DirectBFSSymbolicKernelResidue
import DiophantineConsistency.Compact44.ArithmeticConstructionUnitCompact44
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSModelResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticConstructionUnitCompact44
attribute [local irreducible] DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem residue : ((DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho : ℕ) : V) %
    (DirectBFSSymbolicKernelResidue.Modulus:V) = (264033855341:V) := by
  exact cast_mod_eq DirectBFSSymbolicKernelResidue.symbolic_kernel_mod
#print axioms DirectBFSModelResidue.residue
end DirectBFSModelResidue
