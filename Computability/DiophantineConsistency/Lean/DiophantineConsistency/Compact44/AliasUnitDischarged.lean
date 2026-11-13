import DiophantineConsistency.Compact44.AliasUnitGivenResidue
import DiophantineConsistency.Compact44.AliasResidueNumeral

/-! Uncompiled residue discharge, isolated from the all-model unit theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactAliasUnitDischarged
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticConstructionUnitCompact44
open CompactSymbolicKernelAliasExplicit CompactAliasResidueNumeral CompactAliasUnitGivenResidue

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem alias_unit (m e : V) :
    ∃ Γi, (Gamma (kernelAlias : V) (power 581197 (m + 1)) (power 581197 e) * Γi) %
        (590069 * power 581197 (m + 1)) = 1 % (590069 * power 581197 (m + 1)) := by
  exact alias_unit_given_residue alias_residue_numeral m e

#print axioms alias_unit
end CompactAliasUnitDischarged
