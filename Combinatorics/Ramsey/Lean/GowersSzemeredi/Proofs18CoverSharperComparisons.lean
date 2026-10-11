import GowersSzemeredi.Proofs18CoverSharperExplicit
import GowersSzemeredi.Proofs16PackagedPremisesCounterexample

/-! Strict comparisons for the improved inverse, density, and coloring
constants. These certify that the smaller offsets give stronger bounds
throughout the source's admissible parameter range. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A smaller inverse offset strictly increases the guaranteed exponent. -/
theorem section18ExponentAt_strictAnti {c c' k : Nat} (hc : c < c') {alpha : Real}
    (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    section18ExponentAt c' alpha k < section18ExponentAt c alpha k := by
  have hE : (2 : Nat) ^ ((2 : Nat) ^ (k + c)) <
      (2 : Nat) ^ ((2 : Nat) ^ (k + c')) :=
    Nat.pow_lt_pow_right (by norm_num)
      (Nat.pow_lt_pow_right (by norm_num) (by omega))
  exact pow_lt_pow_right_of_lt_one₀ ha (by linarith) hE

/-- A smaller density offset strictly decreases the required threshold. -/
theorem szemerediThresholdAt_strictMono {c c' k : Nat} (hc : c < c') {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    szemerediThresholdAt c delta k < szemerediThresholdAt c' delta k := by
  have hu : 1 < delta⁻¹ := by
    have h2 : 2 ≤ delta⁻¹ := by rw [← one_div, le_div_iff₀ hδ]; linarith
    linarith
  have hE : (2 : Real) ^ ((2 : Real) ^ (k + c : Nat)) <
      (2 : Real) ^ ((2 : Real) ^ (k + c' : Nat)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      (pow_lt_pow_right₀ (by norm_num) (by omega))
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    (Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      (Real.rpow_lt_rpow_of_exponent_lt hu hE))

/-- The corresponding two-color thresholds decrease strictly as well. -/
theorem twoColorThresholdAt_strictMono {c c' k : Nat} (hc : c < c') :
    twoColorThresholdAt c k < twoColorThresholdAt c' k := by
  have h := szemerediThresholdAt_strictMono (k := k) hc
    (by norm_num : (0 : Real) < 1 / 2) (by norm_num : (1 / 2 : Real) ≤ 1 / 2)
  simpa only [szemerediThresholdAt_half] using h

end LeanProofs.GowersSzemeredi
