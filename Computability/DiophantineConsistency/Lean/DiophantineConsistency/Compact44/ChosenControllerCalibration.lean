import DiophantineConsistency.Compact44.ActualRankCalibration

/-! Bounded attempt: discharge the numerical controller hypotheses for the
same powers used by the halt-to-compact-word dimension construction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactChosenControllerCalibration
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticPackingBlocks
open DiophantineConsistency.ArithmeticConstructionUnitCompact44
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactActualRankCalibration
attribute [local irreducible] paramKernel rho

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact numerical bounds for the selected width and total period. -/
theorem chosen_bounds (T : V) :
    power 581197 (T+1) ≤ power 581197 (2*T+3) ∧
    2*(590069*581197) < power 581197 (2*T+3) ∧
    power 581197 (T+1)*power 581197 (T+3) = power 581197 ((2*T+3)+1) := by
  have hp : (1:V) ≤ 581197 := by norm_num
  have hexp : T+1 ≤ 2*T+3 := by
    calc T+1 ≤ (T+1)+(T+2) := le_add_of_nonneg_right (show (0:V) ≤ T+2 by positivity)
      _ = 2*T+3 := by ring
  have hm : (3:V) ≤ 2*T+3 := by
    simpa only [zero_add] using le_add_of_nonneg_left (show (0:V)≤2*T by positivity)
  have hw := power_mono_exponent 581197 (T+1) (2*T+3) hp hexp
  have h3 : power (581197:V) 3 = 581197*(581197*581197) := by
    rw [show (3:V)=(2:V)+1 by norm_num, power_succ,
      show (2:V)=(1:V)+1 by norm_num, power_succ, power_one]
  have hsize : 2*(590069*581197) < power 581197 (2*T+3) := by
    calc 2*(590069*581197) < power (581197:V) 3 := by rw [h3]; norm_num
      _ ≤ power 581197 (2*T+3) := power_mono_exponent 581197 3 (2*T+3) hp hm
  refine ⟨hw, hsize, ?_⟩
  rw [← power_add]
  congr 1
  ring

/-- Abstract selection for the chosen powers, with no size premise. -/
theorem chosen_calibration (T R0 : V) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) ∧
      (Gamma (paramKernel rho : V) (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) *
        bsum 590069 δ (power 581197 ((2*T+3)+1)) + 590069 * power 581197 (T+1)) %
          (590069 * power 581197 ((2*T+3)+1)) = R0 % (590069 * power 581197 ((2*T+3)+1)) := by
  have h := chosen_bounds T
  exact symbolic_rank_calibration (2*T+3) (T+1) R0 h.2.1 h.1

#print axioms chosen_bounds
#print axioms chosen_calibration
end CompactChosenControllerCalibration
