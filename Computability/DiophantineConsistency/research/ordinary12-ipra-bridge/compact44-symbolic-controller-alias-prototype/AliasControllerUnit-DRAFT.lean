import DiophantineConsistency.ArithmeticConstructionUnitCompact44
import KernelAliasExplicit

/-! Uncompiled: a named-symbol version of the unit theorem; its explicit
equality to paramKernel rho must remain available to every downstream client. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactSymbolicControllerAlias
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticConstructionUnitCompact44
open CompactSymbolicKernelAliasExplicit

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem alias_gamma_unit (m e : V) :
    ∃ Γi, (Gamma (kernelAlias : V) (power 581197 (m + 1)) (power 581197 e) * Γi) %
        (590069 * power 581197 (m + 1)) = 1 % (590069 * power 581197 (m + 1)) := by
  exact gamma_unit_nat kernelAlias kernelAlias_mod m e

#print axioms alias_gamma_unit
end CompactSymbolicControllerAlias
