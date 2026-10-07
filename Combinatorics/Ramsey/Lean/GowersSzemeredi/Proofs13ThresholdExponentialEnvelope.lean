import GowersSzemeredi.Proofs13ExplicitPowerThreshold

/-! Exponential envelopes for the finite positive-power thresholds. These
bounds separate the logarithmic numerator cost from the inverse exponent. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- An exponential cap for the numerator and reciprocal coefficient yields
an exponential cap for the threshold. Zero exponent is allowed, matching
the total definition used at the zero term of finite maxima. -/
theorem positivePowerThreshold_le_exp {C D e A B E : Real}
    (hD : 0 < D) (he : 0 ≤ e) (hAB : 0 ≤ A + B)
    (hC : C ≤ Real.exp A) (hDi : D⁻¹ ≤ Real.exp B) (hEi : e⁻¹ ≤ E) :
    positivePowerThreshold C D e ≤ Real.exp ((A + B) * E) := by
  have hEi0 : 0 ≤ e⁻¹ := inv_nonneg.mpr he
  have hE : 0 ≤ E := hEi0.trans hEi
  have hratio : C / D ≤ Real.exp (A + B) := by
    rw [div_eq_mul_inv, Real.exp_add]
    exact (mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hD.le)).trans
      (mul_le_mul_of_nonneg_left hDi (Real.exp_pos _).le)
  have hbase : max 1 (C / D) ≤ Real.exp (A + B) :=
    max_le (Real.one_le_exp_iff.mpr hAB) hratio
  unfold positivePowerThreshold
  apply max_le (Real.one_le_exp_iff.mpr (mul_nonneg hAB hE))
  calc
    _ ≤ (Real.exp (A + B)) ^ e⁻¹ :=
      Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _)) hbase hEi0
    _ = Real.exp ((A + B) * e⁻¹) := (Real.exp_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hEi hAB)

/-- Polynomial reciprocal bounds give a single-exponential envelope for
one growth threshold; this also covers its zero-exponent finite-sup term. -/
theorem positivePowerThreshold_le_exp_power {C D e x : Real} {a b r : Nat}
    (hx : 1 ≤ x) (hD : 0 < D) (he : 0 ≤ e)
    (hC : C ≤ x ^ a) (hDi : D⁻¹ ≤ x ^ b) (hEi : e⁻¹ ≤ x ^ r) :
    positivePowerThreshold C D e ≤ Real.exp ((a + b : Nat) * x ^ (r + 1)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hClog : C ≤ Real.exp ((a : Real) * Real.log x) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hx0, Real.rpow_natCast]
    exact hC
  have hDlog : D⁻¹ ≤ Real.exp ((b : Real) * Real.log x) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hx0, Real.rpow_natCast]
    exact hDi
  have h := positivePowerThreshold_le_exp hD he (by positivity) hClog hDlog hEi
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hlogx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith only [hx])
  calc
    _ = ((a + b : Nat) : Real) * Real.log x * x ^ r := by push_cast; ring
    _ ≤ ((a + b : Nat) : Real) * x * x ^ r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogx (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- Exponential input budgets yield a double-exponential threshold with
an additive budget in its inner exponent. -/
theorem positivePowerThreshold_le_double_exp {C D e A p q r : Real}
    (hD : 0 < D) (he : 0 ≤ e) (hA : 0 ≤ A) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hC : C ≤ Real.exp (p * A)) (hDi : D⁻¹ ≤ Real.exp (q * A))
    (hEi : e⁻¹ ≤ Real.exp (r * A)) :
    positivePowerThreshold C D e ≤ Real.exp (Real.exp ((p + q + r) * A)) := by
  have h := positivePowerThreshold_le_exp hD he (by positivity) hC hDi hEi
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hlin : p * A + q * A ≤ Real.exp (p * A + q * A) := by
    have ht := Real.add_one_le_exp (p * A + q * A)
    linarith only [ht]
  calc
    _ ≤ Real.exp (p * A + q * A) * Real.exp (r * A) :=
      mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end LeanProofs.GowersSzemeredi
