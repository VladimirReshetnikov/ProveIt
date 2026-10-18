import GowersSzemeredi.Proofs18QuadraticDoubleExponential
import GowersSzemeredi.Proofs18DensityIterationPowerBoundSide
import GowersSzemeredi.Proofs18QuadraticClosedBoundSide
import GowersSzemeredi.Proofs18QuadraticIterationParametersSide

/-! A fixed-power double-exponential bound for the completed quadratic
iteration, with every dependence on the initial density made explicit.

Moved here from `Proofs18QuadraticDoubleExponential`, which keeps only what the
final route uses. -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem quadraticIterationLogBudgetConstant_pos : 0 < quadraticIterationLogBudgetConstant := by
  have h1 := section5LocalRefinementConstant_pos 1 1
  have h2 := section5LocalRefinementConstant_pos 2 1
  unfold quadraticIterationLogBudgetConstant
  linarith only [h1, h2]

theorem quadraticIntervalClosedThreshold_le_double_exp_alpha {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    quadraticIntervalClosedThreshold delta ≤
      Real.exp (Real.exp ((quadraticIterationLogBudgetConstant + 1) *
        (2 / intervalQuadraticUniformityParameter delta) ^ (25378984 : Nat))) := by
  have hα := intervalQuadraticUniformityParameter_pos hδ
  have hαone := intervalQuadraticUniformityParameter_le_one hδ.le hδone
  obtain ⟨_, hg, hr, _⟩ := quadratic_interval_parameters_inv_upper hα hαone
  exact densityIterationClosedThreshold_le_double_exp _ _ _ _ _ _ 12384 24748 25378984
    (intervalQuadratic_constants_pos hδ).1
    ((le_div_iff₀ hα).mpr (by linarith))
    (quadratic_iteration_log_budget hδ hδone) hg hr (by norm_num)

theorem quadraticIntervalClosedThreshold_le_double_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    quadraticIntervalClosedThreshold delta ≤
      Real.exp (Real.exp ((quadraticIterationLogBudgetConstant + 1) *
        (2 / delta) ^ (3070857064 : Nat))) := by
  have hα := intervalQuadraticUniformityParameter_pos hδ
  apply (quadraticIntervalClosedThreshold_le_double_exp_alpha hδ hδone).trans
  apply Real.exp_le_exp.mpr
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by have := quadraticIterationLogBudgetConstant_pos; linarith)
  calc
    _ ≤ ((2 / delta) ^ (121 : Nat)) ^ (25378984 : Nat) :=
      pow_le_pow_left₀ (by positivity) (intervalQuadraticUniformityParameter_inv_upper hδ hδone).2 _
    _ = _ := by rw [← pow_mul]

theorem quadratic_cyclic_szemeredi_double_exp
    (delta : Real) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (N : Nat) [NeZero N]
    (hN : Real.exp (Real.exp ((quadraticIterationLogBudgetConstant + 1) *
      (2 / delta) ^ (3070857064 : Nat))) ≤ N)
    (A : Finset (ZMod N)) (hcard : delta * N ≤ A.card) : HasModAP A 4 :=
  quadratic_cyclic_szemeredi_closed delta hδ hδone N
    ((quadraticIntervalClosedThreshold_le_double_exp hδ hδone).trans hN) A hcard

end LeanProofs.GowersSzemeredi
