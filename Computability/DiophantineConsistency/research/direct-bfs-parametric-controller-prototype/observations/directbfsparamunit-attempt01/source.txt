import DirectBFSControllerUnit
import DirectBFSSymbolicKernelResidue
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSParametricController
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPow ArithmeticConstructionUnitCompact44
attribute [local irreducible] DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem unit_of_residue (r : ℕ) (h : DirectBFSSymbolicKernel.paramKernel r %
    342946332593 = 264033855341) (m e : V) :
    ∃ Γi, (Gamma (DirectBFSSymbolicKernel.paramKernel r : V) (power 581197 (m+1))
        (power 581197 e) * Γi) % (590069 * power 581197 (m+1)) =
        1 % (590069 * power 581197 (m+1)) := by
  exact DirectBFSControllerUnit.bfs_gamma_unit_nat _ h m e

theorem symbolic_unit (m e : V) :
    ∃ Γi, (Gamma (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho : V)
        (power 581197 (m+1)) (power 581197 e) * Γi) %
        (590069 * power 581197 (m+1)) = 1 % (590069 * power 581197 (m+1)) := by
  exact unit_of_residue CompactSymbolicKernel.rho DirectBFSSymbolicKernelResidue.symbolic_kernel_mod m e
#print axioms DirectBFSParametricController.unit_of_residue
#print axioms DirectBFSParametricController.symbolic_unit
end DirectBFSParametricController
