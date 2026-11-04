import DiophantineConsistency.Compact44.AliasRankCalibration

/-! Bounded attempt to transport the abstract calibration to the exact
symbolic K. Physical packing and the rank-variation equation remain separate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactActualRankCalibration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticPackingBlocks
open DiophantineConsistency.ArithmeticConstructionUnitCompact44
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicKernelAliasExplicit
open CompactAliasRankCalibration
attribute [local irreducible] paramKernel rho

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem symbolic_rank_calibration (m e R0 : V)
    (hP2 : 2 * (590069 * 581197) < power 581197 m)
    (hw : power 581197 e ≤ power 581197 m) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 (m + 1) ∧
        j + power 581197 e < power 581197 (m + 1)) ∧
      (Gamma (paramKernel rho : V) (power 581197 (m + 1)) (power 581197 e) *
        bsum 590069 δ (power 581197 (m + 1)) + 590069 * power 581197 e) %
          (590069 * power 581197 (m + 1)) = R0 % (590069 * power 581197 (m + 1)) := by
  exact (congrArg (fun k : ℕ => ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
    (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 (m + 1) ∧
      j + power 581197 e < power 581197 (m + 1)) ∧
    (Gamma (k : V) (power 581197 (m + 1)) (power 581197 e) *
      bsum 590069 δ (power 581197 (m + 1)) + 590069 * power 581197 e) %
        (590069 * power 581197 (m + 1)) = R0 % (590069 * power 581197 (m + 1)))
    kernelAlias_eq).mp (alias_rank_calibration m e R0 hP2 hw)

#print axioms symbolic_rank_calibration
end CompactActualRankCalibration
