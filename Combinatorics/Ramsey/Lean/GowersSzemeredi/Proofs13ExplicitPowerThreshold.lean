import GowersSzemeredi.Proofs13LargeScaleBudgets

/-! Explicit thresholds for the positive-power growth conditions used in
Section 13. The definitions contain no chosen eventual-growth witnesses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A finite threshold ensuring C <= D*x^e for positive D and e. -/
def positivePowerThreshold (C D e : Real) : Real :=
  max 1 ((max 1 (C / D)) ^ e⁻¹)

theorem positivePowerThreshold_one_le (C D e : Real) :
    1 ≤ positivePowerThreshold C D e := le_max_left _ _

/-- Equality is allowed at the threshold, with no sign restriction on C. -/
theorem positivePowerThreshold_spec {C D e x : Real} (hD : 0 < D) (he : 0 < e)
    (hx : positivePowerThreshold C D e ≤ x) : C ≤ D * x ^ e := by
  have hbase : 0 ≤ max 1 (C / D) := le_trans zero_le_one (le_max_left _ _)
  have hp : max 1 (C / D) ≤ x ^ e := by
    calc
      _ = ((max 1 (C / D)) ^ e⁻¹) ^ e := (Real.rpow_inv_rpow hbase he.ne').symm
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) ((le_max_right _ _).trans hx) he.le
  have hratio : C / D ≤ x ^ e := (le_max_right _ _).trans hp
  have h := (div_le_iff₀ hD).mp hratio
  simpa only [mul_comm] using h

end LeanProofs.GowersSzemeredi
