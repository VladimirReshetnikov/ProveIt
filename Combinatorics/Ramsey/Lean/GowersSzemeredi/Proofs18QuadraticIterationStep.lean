import GowersSzemeredi.Proofs18IntervalQuadraticDichotomy
import GowersSzemeredi.Proofs18GeneralIterationStep
import Mathlib.NumberTheory.Bertrand

/-! A prime-free density increment with constants fixed by the initial
density lower bound. Later stages may have greater actual density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def intervalQuadraticGain (delta : Real) : Real :=
  quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) / 8

def intervalQuadraticLengthExponent (delta : Real) : Real :=
  quadraticDiscrepancyExponent (intervalQuadraticUniformityParameter delta) / 16

def intervalQuadraticLengthFactor (delta : Real) : Real :=
  quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) /
    (8 * boundaryRefinementConstant
      (quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) / 64))

def intervalQuadraticStepThreshold (delta : Real) : Real :=
  max 4 (max (quadraticExponentialThreshold (intervalQuadraticUniformityParameter delta))
    (max (32 / quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta))
      (8193 / delta ^ 4)))

theorem intervalQuadratic_constants_pos {delta : Real} (hδ : 0 < delta) :
    0 < intervalQuadraticGain delta ∧ 0 < intervalQuadraticLengthExponent delta ∧
      0 < intervalQuadraticLengthFactor delta := by
  have hα := intervalQuadraticUniformityParameter_pos hδ
  have hτ : 0 < quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) := by
    unfold quadraticDiscrepancyParameter
    positivity
  have hC := section5LocalRefinementConstant_pos 1
    (4 * Real.pi * (quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) / 64))
  refine ⟨div_pos hτ (by norm_num), ?_, div_pos hτ (mul_pos (by norm_num) hC)⟩
  unfold intervalQuadraticLengthExponent quadraticDiscrepancyExponent cor711Exponent
  positivity

/-- Choose a comparable prime, use the fixed initial uniformity parameter,
and reindex the selected progression. No primality condition remains in the
iteration interface, and the lower density d may increase at every step. -/
theorem interval_quadratic_iteration_step
    (delta : Real) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (L : Nat) (hL : intervalQuadraticStepThreshold delta ≤ L)
    (B : Finset (Fin L)) (d : Real) (hd : delta ≤ d) (hcard : d * L ≤ B.card) :
    HasNatAP (B.image Fin.val) 4 ∨
      ∃ l : Nat, ∃ B' : Finset (Fin l),
        intervalQuadraticLengthFactor delta * (L : Real) ^ intervalQuadraticLengthExponent delta ≤ l ∧
        (d + intervalQuadraticGain delta) * l ≤ B'.card ∧
        (HasNatAP (B'.image Fin.val) 4 → HasNatAP (B.image Fin.val) 4) := by
  have hα := intervalQuadraticUniformityParameter_pos hδ
  have hαone := intervalQuadraticUniformityParameter_le_one hδ.le hδone
  have hαeq : intervalUniformityParameter delta 4 =
      intervalQuadraticUniformityParameter delta := by
    norm_num [intervalUniformityParameter, intervalQuadraticUniformityParameter]
  have hbound := quadratic_function_discrepancy_bound hα hαone
  rw [← hαeq] at hα hbound
  have hstep := hbound.interval_density_step (by norm_num : 2 ≤ 4) hδ
    (by unfold quadraticDiscrepancyParameter; positivity)
    (by unfold quadraticDiscrepancyExponent cor711Exponent; positivity)
  rw [hαeq] at hstep
  apply hstep L ?_ B d hd hcard
  simpa only [intervalDiscrepancyStepThreshold, intervalQuadraticStepThreshold,
    Nat.cast_ofNat, show (512 : Real) * 4 ^ (2 : Nat) + 1 = 8193 by norm_num] using hL

end LeanProofs.GowersSzemeredi
