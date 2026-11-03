import DiophantineConsistency.ArithmeticConstructionUnitCompact44
import KernelAliasExplicit

/-! Uncompiled named-kernel unit with an explicit natural residue premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactAliasUnitGivenResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticConstructionUnitCompact44
open CompactSymbolicKernelAliasExplicit

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem alias_unit_given_residue (h : kernelAlias % 342946332593 = 284898815895) (m e : V) :
    ∃ Γi, (Gamma (kernelAlias : V) (power 581197 (m + 1)) (power 581197 e) * Γi) %
        (590069 * power 581197 (m + 1)) = 1 % (590069 * power 581197 (m + 1)) := by
  exact gamma_unit_nat kernelAlias h m e

#print axioms alias_unit_given_residue
end CompactAliasUnitGivenResidue
