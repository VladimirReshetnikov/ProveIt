import GowersSzemeredi.Proofs18DensityIterationPowerBound
import GowersSzemeredi.Proofs18QuadraticIterationParameters
import GowersSzemeredi.Proofs18QuadraticClosedBound

/-! A fixed-power double-exponential bound for the completed quadratic
iteration, with every dependence on the initial density made explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def quadraticIterationLogBudgetConstant : Real :=
  (4 + 6 * section5LocalRefinementConstant 2 1) + 8230 + 8 * section5LocalRefinementConstant 1 1

theorem quadraticIterationLogBudgetConstant_pos : 0 < quadraticIterationLogBudgetConstant := by
  have h1 := section5LocalRefinementConstant_pos 1 1
  have h2 := section5LocalRefinementConstant_pos 2 1
  unfold quadraticIterationLogBudgetConstant
  linarith only [h1, h2]

theorem quadratic_iteration_log_budget {delta : Real} (hδ : 0 < delta) (hδone : delta ≤ 1) :
    1 + Real.log (max 1 (intervalQuadraticStepThreshold delta)) +
        |Real.log (intervalQuadraticLengthFactor delta)| ≤
      quadraticIterationLogBudgetConstant *
        (2 / intervalQuadraticUniformityParameter delta) ^ (25378984 : Nat) := by
  let alpha := intervalQuadraticUniformityParameter delta
  let u := 2 / alpha
  let D := 4 + 6 * section5LocalRefinementConstant 2 1
  let E := D + 8229
  let C := 8 * section5LocalRefinementConstant 1 1
  have hα : 0 < alpha := intervalQuadraticUniformityParameter_pos hδ
  have hαone : alpha ≤ 1 := intervalQuadraticUniformityParameter_le_one hδ.le hδone
  have hD : 0 < D := by dsimp [D]; have := section5LocalRefinementConstant_pos 2 1; positivity
  have hC : 0 < C := by dsimp [C]; exact mul_pos (by norm_num) (section5LocalRefinementConstant_pos _ _)
  have hu : 2 ≤ u := (le_div_iff₀ hα).mpr (by linarith)
  have huone : 1 ≤ u := by linarith
  have hupow : 1 ≤ u ^ (25378984 : Nat) := one_le_pow₀ huone
  have huP : u ≤ u ^ (25378984 : Nat) := by
    simpa only [pow_one] using pow_le_pow_right₀ huone (by norm_num : 1 ≤ 25378984)
  obtain ⟨hτ, _, _, hc⟩ := quadratic_interval_parameters_inv_upper hα hαone
  have hτP : (quadraticDiscrepancyParameter alpha)⁻¹ ≤ u ^ (25378984 : Nat) :=
    hτ.trans (pow_le_pow_right₀ huone (by norm_num : 12381 ≤ 25378984))
  have hd4 : (delta ^ 4)⁻¹ ≤ u := by
    calc
      _ ≤ alpha⁻¹ := (inv_le_inv₀ (pow_pos hδ 4) hα).mpr
        (intervalQuadraticUniformityParameter_le_pow_four hδ.le hδone)
      _ ≤ _ := by dsimp [u]; rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr hα]
  have hlin : E * u ^ (25378984 : Nat) ≤ Real.exp (E * u ^ (25378984 : Nat)) :=
    (le_add_of_nonneg_right (by norm_num : (0 : Real) ≤ 1)).trans (Real.add_one_le_exp _)
  have hT : intervalQuadraticStepThreshold delta ≤ Real.exp (E * u ^ (25378984 : Nat)) := by
    unfold intervalQuadraticStepThreshold
    apply max_le
    · apply le_trans _ hlin
      calc
        (4 : Real) ≤ E := by dsimp [E]; linarith only [hD]
        _ ≤ E * u ^ (25378984 : Nat) := le_mul_of_one_le_right
          (by dsimp [E]; linarith only [hD]) hupow
    · apply max_le
      · change Real.exp (D * u ^ (25378984 : Nat)) ≤ _
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (by dsimp [E]; linarith) (by positivity)
      · apply max_le
        · calc
            _ ≤ 32 * u ^ (25378984 : Nat) := by
              rw [div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_left hτP (by norm_num)
            _ ≤ E * u ^ (25378984 : Nat) :=
              mul_le_mul_of_nonneg_right (by dsimp [E]; linarith) (by positivity)
            _ ≤ _ := hlin
        · calc
            _ ≤ 8193 * u := by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hd4 (by norm_num)
            _ ≤ 8193 * u ^ (25378984 : Nat) := mul_le_mul_of_nonneg_left huP (by norm_num)
            _ ≤ E * u ^ (25378984 : Nat) :=
              mul_le_mul_of_nonneg_right (by dsimp [E]; linarith) (by positivity)
            _ ≤ _ := hlin
  have hTfour : 4 ≤ intervalQuadraticStepThreshold delta := le_max_left _ _
  have hlogT : Real.log (max 1 (intervalQuadraticStepThreshold delta)) ≤ E * u ^ (25378984 : Nat) := by
    rw [max_eq_right (by linarith : 1 ≤ intervalQuadraticStepThreshold delta)]
    exact (Real.log_le_iff_le_exp (by linarith)).mpr hT
  have hcpos := (intervalQuadratic_constants_pos hδ).2.2
  have hcone : intervalQuadraticLengthFactor delta ≤ 1 := quadratic_interval_length_factor_le_one hα hαone
  have hlogc : |Real.log (intervalQuadraticLengthFactor delta)| ≤ C * u ^ (25378984 : Nat) := by
    calc
      _ = -Real.log (intervalQuadraticLengthFactor delta) :=
        abs_of_nonpos (Real.log_nonpos hcpos.le hcone)
      _ = Real.log (intervalQuadraticLengthFactor delta)⁻¹ := (Real.log_inv _).symm
      _ ≤ (intervalQuadraticLengthFactor delta)⁻¹ := Real.log_le_self (inv_nonneg.mpr hcpos.le)
      _ ≤ C * u ^ (210541 : Nat) := hc
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ huone (by norm_num : 210541 ≤ 25378984)) hC.le
  change _ ≤ quadraticIterationLogBudgetConstant * u ^ (25378984 : Nat)
  have heq : quadraticIterationLogBudgetConstant = 1 + E + C := by
    dsimp [quadraticIterationLogBudgetConstant, E, D, C]
    ring
  rw [heq]
  nlinarith only [hlogT, hlogc, hupow]

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
