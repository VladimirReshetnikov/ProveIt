import DiophantineConsistency.ArithmeticConstructionUnitCompact44
import SymbolicKernelResidue

/-! Uncompiled same-provider client: the concrete symbolic K discharges the
previously conditional controller-unit residue premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicControllerJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticConstructionUnitCompact44
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicKernelResidue

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem symbolic_gamma_unit (m e : V) :
    ∃ Γi, (Gamma (paramKernel rho : V) (power 581197 (m + 1)) (power 581197 e) * Γi) %
        (590069 * power 581197 (m + 1)) = 1 % (590069 * power 581197 (m + 1)) := by
  exact gamma_unit_nat (paramKernel rho) symbolic_kernel_mod m e

#print axioms symbolic_gamma_unit
end CompactSymbolicControllerJoin
