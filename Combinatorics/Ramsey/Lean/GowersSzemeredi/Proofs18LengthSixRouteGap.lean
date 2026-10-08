import GowersSzemeredi.Proofs18ExplicitQuarticInverse
import GowersSzemeredi.Proofs18GeneralIteration
import GowersSzemeredi.Proofs18FejerIterationParameters
import GowersSzemeredi.Sections17_18

/-! The proved route cannot give Theorem 18.2 at length six and density 1/2.

Research notes K.4. The proved degree-four inverse theorem
(`quartic_function_inverse_explicit`) has discrepancy parameter
`β = jointStructuralInverseParameter 2 α`, where
`α = intervalUniformityParameter (1/2) 6`. This module proves that the
density iteration's closed threshold at that `β`, for **any** `σ > 0` and
`T`, exceeds `szemerediThreshold (1/2) 6`. So `Section18DiscrepancyBudget`
cannot be discharged at `(1/2, 6)` from this inverse theorem, and Corollary
18.7 at `k = 6` does not follow from it.

The argument uses only crude facts.

* `β ≤ 1/G`, where `G` is the joint graph budget.
* `G ≥ q₀^(r·s)` with `q₀ ≥ 2`, and `s ≥ 2^(2^(2^(k+6)))` at `k = 2`.
* The threshold is at least `exp(2^(8/β))`.

All towers stay symbolic, so nothing large is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A control-function value `q(x, γ, k)` is at least two once `γ x ≤ 1/2`. -/
theorem two_le_multipleQ {x gamma : Real} (k : Nat) (hx : 0 < x) (hg : 0 < gamma)
    (hgx : gamma * x ≤ 1 / 2) : 2 ≤ multipleQ x gamma k := by
  unfold multipleQ multipleC
  have h0 : 0 < gamma * x := mul_pos hg hx
  have hA : 1 ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 8)) := Nat.one_le_two_pow
  have hle : (gamma * x) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) ≤ gamma * x :=
    pow_le_of_le_one h0.le (by linarith) (by omega)
  have hpos : 0 < (gamma * x) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 8))) := pow_pos h0 _
  rw [le_inv_comm₀ (by norm_num) hpos]
  linarith

/-- The slice budget of the power profile is at least `2^(2^(2^(k+6)))`. -/
theorem section16PowerSliceBudget_ge {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) ≤ section16PowerSliceBudget theta gamma k := by
  unfold section16PowerSliceBudget multipleS
  have hθ' : 0 < (2 : Real) ^ (-(k + 2 : Real)) * theta := by positivity
  have hθ'1 : (2 : Real) ^ (-(k + 2 : Real)) * theta ≤ 1 := by
    have h2 : (2 : Real) ^ (-(k + 2 : Real)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [(Nat.cast_nonneg k : (0 : Real) ≤ k)])
    nlinarith
  have hbase : (2 : Real) ≤ 2 / ((2 : Real) ^ (-(k + 2 : Real)) * theta * gamma) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hpow : (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) ≤
      (2 / ((2 : Real) ^ (-(k + 2 : Real)) * theta * gamma)) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) :=
    pow_le_pow_left₀ (by norm_num) hbase _
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (by positivity)).mpr (pow_le_one₀ hg.le hg1)
  have hS0 : 0 ≤ (2 / ((2 : Real) ^ (-(k + 2 : Real)) * theta * gamma)) ^
      ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) := by positivity
  calc (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) ≤ _ := hpow
    _ ≤ gamma ^ (-(2 : Int)) * (2 / ((2 : Real) ^ (-(k + 2 : Real)) * theta * gamma)) ^
        ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) := le_mul_of_one_le_left hS0 hginv

/-- The joint graph budget is at least `2^(r·s) ≥ 2^(2^(2^(2^(k+6))))`. -/
theorem section16JointPowerGraphBudget_ge {alpha : Real} (k : Nat)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1 / 2) :
    (2 : Real) ^ ((2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)))) ≤
      section16JointPowerGraphBudget (alpha / 8) (alpha / 4) (alpha / 2) k := by
  set θ := alpha / 4 with hθdef
  set γ := alpha / 2 with hγdef
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by rw [hθdef]; linarith
  have hγ0 : 0 < γ := by rw [hγdef]; positivity
  have hγ4 : γ ≤ 1 / 4 := by rw [hγdef]; linarith
  set σ := section16JointPowerLoss (alpha / 8) θ γ k / 4 with hσdef
  set s := section16PowerSliceBudget θ γ k
  set r := section16UniformSampleCount σ θ γ k
  have hσ0 : 0 < σ := by
    have := section16JointPowerLoss_pos (theta := θ) (gamma := γ) k (by positivity : 0 < alpha / 8)
    positivity
  have hσ1 : σ ≤ 1 := by
    have := section16JointPowerLoss_le_one (theta := θ) (gamma := γ) k (by linarith : alpha / 8 ≤ 1)
    rw [hσdef]; linarith
  have hs : (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) ≤ s :=
    section16PowerSliceBudget_ge k hθ0 hθ1 hγ0 (by linarith)
  have hs1 : 1 ≤ s := le_trans (one_le_pow₀ (by norm_num)) hs
  have hr : (1 : Real) ≤ r := by
    exact_mod_cast section16UniformSampleCount_pos (theta := θ) (gamma := γ) k hσ0
  have hrs : s ≤ (r : Real) * s := le_mul_of_one_le_left (by linarith) hr
  have hrs0 : 0 < (r : Real) * s := by positivity
  set x := ((r : Real) * s)⁻¹ * σ
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    have : ((r : Real) * s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hs1.trans hrs)
    nlinarith
  have hq : 2 ≤ multipleQ x γ k :=
    two_le_multipleQ k hx0 hγ0 (by nlinarith [mul_le_mul hγ4 hx1 hx0.le (by norm_num : (0:Real) ≤ 1 / 4)])
  -- the max in the uniform-lift budget is at least its first entry
  have hb : (2 : Real) ^ ((r : Real) * s) ≤ section16UniformLiftGraphBudget σ θ γ s k := by
    unfold section16UniformLiftGraphBudget
    refine le_trans ?_ (le_max_left _ _)
    exact Real.rpow_le_rpow (by norm_num) hq hrs0.le
  have hpiece : (1 : Real) ≤ (section16PowerPieceBudget θ γ k : Real) := by
    have hp := section16CommonBasePieceBound_pos (theta := θ) (gamma := γ) k hθ0 hγ0
    have : 0 < section16PowerPieceBudget θ γ k := by
      unfold section16PowerPieceBudget; exact Nat.ceil_pos.mpr hp
    exact_mod_cast this
  have hULGB0 : 0 ≤ section16UniformLiftGraphBudget σ θ γ s k :=
    le_trans (by positivity) hb
  have hexp : (2 : Real) ^ ((2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)))) ≤ (2 : Real) ^ ((r : Real) * s) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hs.trans hrs)
  unfold section16JointPowerGraphBudget
  calc _ ≤ (2 : Real) ^ ((r : Real) * s) := hexp
    _ ≤ section16UniformLiftGraphBudget σ θ γ s k := hb
    _ ≤ _ := le_mul_of_one_le_left hULGB0 hpiece

/-- The degree-four discrepancy parameter is at most the joint frequency
density. -/
theorem jointStructuralInverseParameter_two_le {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1 / 2) :
    jointStructuralInverseParameter 2 alpha ≤ section16JointFrequencyDensity alpha 2 := by
  have hin : structuralInverseInput alpha = alpha := min_eq_left ha1
  have hy := jointStructuralInverseLowerInput_pos ha 2
  have hfej : jointStructuralInverseParameter 1 (jointStructuralInverseLowerInput alpha 2) ≤ 1 := by
    show fejerCubicDiscrepancyParameter (structuralInverseInput (jointStructuralInverseLowerInput alpha 2)) ≤ 1
    exact fejerCubicDiscrepancyParameter_le_one (structuralInverseInput_pos hy)
      ((min_le_right _ _).trans (by norm_num))
  have hJ := section16JointFrequencyDensity_pos ha 2
  have hloc : jointPowerLocalizationParameter alpha 2 ≤ section16JointFrequencyDensity alpha 2 := by
    unfold jointPowerLocalizationParameter
    have h1 : (2 : Real) ^ (-(2 * (2 + 2) ^ 3 : Int)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
    have h2 : alpha ^ 2 / 4 ≤ 1 := by nlinarith
    have h3 : section16JointFrequencyDensity alpha 2 / (2 : Real) ^ (2 + 1) * alpha ^ 2 / 4 ≤
        section16JointFrequencyDensity alpha 2 := by
      have hd : section16JointFrequencyDensity alpha 2 / (2 : Real) ^ (2 + 1) ≤
          section16JointFrequencyDensity alpha 2 := div_le_self hJ.le (by norm_num)
      calc section16JointFrequencyDensity alpha 2 / (2 : Real) ^ (2 + 1) * alpha ^ 2 / 4
          = section16JointFrequencyDensity alpha 2 / (2 : Real) ^ (2 + 1) * (alpha ^ 2 / 4) := by ring
        _ ≤ section16JointFrequencyDensity alpha 2 / (2 : Real) ^ (2 + 1) * 1 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ _ := by rw [mul_one]; exact hd
    have h4 : 0 ≤ section16JointFrequencyDensity alpha 2 / (2 : Real) ^ (2 + 1) * alpha ^ 2 / 4 := by
      positivity
    calc (2 : Real) ^ (-(2 * (2 + 2) ^ 3 : Int)) *
          (section16JointFrequencyDensity alpha 2 / (2 : Real) ^ (2 + 1) * alpha ^ 2 / 4)
        ≤ 1 * (section16JointFrequencyDensity alpha 2 / (2 : Real) ^ (2 + 1) * alpha ^ 2 / 4) :=
          mul_le_mul_of_nonneg_right h1 h4
      _ ≤ _ := by rw [one_mul]; exact h3
  have hloc0 : 0 ≤ jointPowerLocalizationParameter alpha 2 :=
    (jointPowerLocalizationParameter_pos ha 2).le
  show jointPowerLocalizationParameter (structuralInverseInput alpha) 2 *
      jointStructuralInverseParameter 1 (jointStructuralInverseLowerInput alpha 2) / 4 ≤ _
  rw [hin]
  have hprod : jointPowerLocalizationParameter alpha 2 *
      jointStructuralInverseParameter 1 (jointStructuralInverseLowerInput alpha 2) ≤
        jointPowerLocalizationParameter alpha 2 := by
    calc _ ≤ jointPowerLocalizationParameter alpha 2 * 1 := mul_le_mul_of_nonneg_left hfej hloc0
      _ = _ := mul_one _
  linarith

/-- **K.4, kernel-checked.** At length six and density one half, the
density iteration's closed threshold for the proved degree-four parameter
exceeds the source threshold, whatever the remaining constants. -/
theorem lengthSix_half_density_route_exceeds (sigma T : Real) :
    szemerediThreshold (1 / 2) 6 <
      intervalDiscrepancyClosedThreshold 6 (1 / 2)
        (jointStructuralInverseParameter 2 (intervalUniformityParameter (1 / 2) 6)) sigma T := by
  set alpha := intervalUniformityParameter (1 / 2) 6 with hαdef
  have hα0 : 0 < alpha := intervalUniformityParameter_pos (by norm_num) (by norm_num)
  have hα1 : alpha ≤ 1 / 2 := by
    rw [hαdef]; unfold intervalUniformityParameter
    have hb0 : (0 : Real) ≤ (1 / 2 : Real) ^ 6 / (512 * ((6 : Nat) : Real) ^ 3) := by positivity
    have hb : (1 / 2 : Real) ^ 6 / (512 * ((6 : Nat) : Real) ^ 3) ≤ 1 / 2 := by norm_num
    calc ((1 / 2 : Real) ^ 6 / (512 * ((6 : Nat) : Real) ^ 3)) ^ ((2 : Nat) ^ (6 - 1))
        ≤ (1 / 2 : Real) ^ 6 / (512 * ((6 : Nat) : Real) ^ 3) :=
          pow_le_of_le_one hb0 (by linarith) (by norm_num)
      _ ≤ 1 / 2 := hb
  set beta := jointStructuralInverseParameter 2 alpha with hβdef
  have hβ0 : 0 < beta := jointStructuralInverseParameter_pos 2 hα0
  set G := section16JointPowerGraphBudget (alpha / 8) (alpha / 4) (alpha / 2) 2 with hGdef
  have hW := section16JointPowerGraphBudget_ge (alpha := alpha) 2 hα0 hα1
  rw [← hGdef] at hW
  have hG0 : 0 < G := lt_of_lt_of_le (by positivity) hW
  have hβG : beta ≤ G⁻¹ := by
    have h := jointStructuralInverseParameter_two_le hα0 hα1
    unfold section16JointFrequencyDensity at h
    rw [← hGdef] at h
    calc beta ≤ alpha / 8 / G := h
      _ ≤ 1 / G := div_le_div_of_nonneg_right (by linarith) hG0.le
      _ = G⁻¹ := one_div G
  set n := ⌈(beta / 8)⁻¹⌉₊ with hndef
  have hn : 8 * G ≤ (n : Real) := by
    have hGβ : G * beta ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hβG hG0.le
      rwa [mul_inv_cancel₀ hG0.ne'] at this
    have h1 : 8 * G ≤ (beta / 8)⁻¹ := by
      rw [inv_div, le_div_iff₀ hβ0]
      linarith
    exact h1.trans (Nat.le_ceil _)
  have hthr : Real.exp ((2 : Real) ^ n) ≤
      intervalDiscrepancyClosedThreshold 6 (1 / 2) beta sigma T := by
    unfold intervalDiscrepancyClosedThreshold densityIterationClosedThreshold
    apply Real.exp_le_exp.mpr
    set a := 1 + Real.log (max 1 (intervalDiscrepancyStepThreshold 6 (1 / 2) beta T)) +
      |Real.log (beta / (8 * boundaryRefinementConstant (beta / 64)))|
    have ha1 : 1 ≤ a := by
      have h1 : 0 ≤ Real.log (max 1 (intervalDiscrepancyStepThreshold 6 (1 / 2) beta T)) :=
        Real.log_nonneg (le_max_left _ _)
      have h2 := abs_nonneg (Real.log (beta / (8 * boundaryRefinementConstant (beta / 64))))
      linarith
    have hb : (2 : Real) ^ n ≤ (2 * max 1 (sigma / 16)⁻¹) ^ n :=
      pow_le_pow_left₀ (by norm_num) (by linarith [le_max_left (1 : Real) (sigma / 16)⁻¹]) n
    have hb0 : (0 : Real) ≤ (2 : Real) ^ n := by positivity
    calc (2 : Real) ^ n ≤ (2 * max 1 (sigma / 16)⁻¹) ^ n := hb
      _ = 1 * (2 * max 1 (sigma / 16)⁻¹) ^ n := (one_mul _).symm
      _ ≤ a * (2 * max 1 (sigma / 16)⁻¹) ^ n :=
          mul_le_mul_of_nonneg_right ha1 (hb0.trans hb)
  set E := ((1 / 2 : Real)⁻¹) ^ ((2 : Real) ^ ((2 : Real) ^ (6 + 9 : Nat))) with hEdef
  have hE : E < (n : Real) := by
    have hinv : ((1 / 2 : Real)⁻¹) = 2 := by norm_num
    have h15 : (2 : Real) ^ ((2 : Real) ^ (6 + 9 : Nat)) ≤
        (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6))) := by
      rw [← Real.rpow_natCast (2 : Real) ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6)))]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hle : (6 + 9 : Nat) ≤ (2 : Nat) ^ (2 + 6) := by norm_num
      have h := pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hle
      exact_mod_cast h
    have hEW : E ≤ (2 : Real) ^ ((2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6)))) := by
      rw [hEdef, hinv]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h15
    have hpos : 0 < (2 : Real) ^ ((2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (2 + 6)))) := by positivity
    linarith
  have hsz : szemerediThreshold (1 / 2) 6 = (2 : Real) ^ ((2 : Real) ^ E) := by
    unfold szemerediThreshold; rfl
  rw [hsz]
  calc (2 : Real) ^ ((2 : Real) ^ E) < (2 : Real) ^ ((2 : Real) ^ (n : Real)) := by
        apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hE
    _ ≤ Real.exp ((2 : Real) ^ (n : Real)) := two_rpow_le_exp (by positivity)
    _ = Real.exp ((2 : Real) ^ n) := by rw [Real.rpow_natCast]
    _ ≤ _ := hthr

end LeanProofs.GowersSzemeredi
