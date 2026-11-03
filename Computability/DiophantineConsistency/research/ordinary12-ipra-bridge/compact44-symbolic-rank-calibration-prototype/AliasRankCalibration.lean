import DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle
import AliasUnitDischarged

/-! Bounded attempt: combine abstract controller calibration with the unit of
the proved equal symbolic alias. This does not assert physical dummy safety. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactAliasRankCalibration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticPackingBlocks
open DiophantineConsistency.ArithmeticConstructionUnitCompact44
open DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle
open CompactSymbolicKernelAliasExplicit CompactAliasUnitDischarged

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem alias_rank_calibration (m e R0 : V)
    (hP2 : 2 * (590069 * 581197) < power 581197 m)
    (hw : power 581197 e ≤ power 581197 m) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 (m + 1) ∧
        j + power 581197 e < power 581197 (m + 1)) ∧
      (Gamma (kernelAlias : V) (power 581197 (m + 1)) (power 581197 e) *
        bsum 590069 δ (power 581197 (m + 1)) + 590069 * power 581197 e) %
          (590069 * power 581197 (m + 1)) = R0 % (590069 * power 581197 (m + 1)) := by
  obtain ⟨Γi, hΓ⟩ := alias_unit m e
  exact rank_calibration m (power 581197 e) R0
    (Gamma (kernelAlias : V) (power 581197 (m + 1)) (power 581197 e)) Γi hP2 hw hΓ

#print axioms alias_rank_calibration
end CompactAliasRankCalibration
