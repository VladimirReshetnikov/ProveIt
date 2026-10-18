import GowersSzemeredi.Proofs13ThresholdExponentialEnvelope

/-! Declarations of `Proofs13ThresholdExponentialEnvelope` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

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

end LeanProofs.GowersSzemeredi
