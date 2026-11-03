import DirectBFSControllerUnit
import DirectBFSSymbolicKernelResidue
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSSymbolicControllerUnit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow ArithmeticConstructionUnitCompact44
attribute [local irreducible] DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho

@[irreducible] def kernelAlias : ℕ := DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho

theorem kernelAlias_eq : kernelAlias = DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho := by
  unfold kernelAlias
  rfl

theorem kernelAlias_mod : kernelAlias % 342946332593 = 264033855341 := by
  exact (congrArg (fun k : ℕ => k % 342946332593 = 264033855341) kernelAlias_eq).mpr
    DirectBFSSymbolicKernelResidue.symbolic_kernel_mod

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem symbolic_unit (m e : V) :
    ∃ Γi, (Gamma (kernelAlias : V) (power 581197 (m+1)) (power 581197 e) * Γi) %
        (590069 * power 581197 (m+1)) = 1 % (590069 * power 581197 (m+1)) := by
  exact DirectBFSControllerUnit.bfs_gamma_unit_nat kernelAlias kernelAlias_mod m e
#print axioms DirectBFSSymbolicControllerUnit.kernelAlias_eq
#print axioms DirectBFSSymbolicControllerUnit.kernelAlias_mod
#print axioms DirectBFSSymbolicControllerUnit.symbolic_unit
end DirectBFSSymbolicControllerUnit
