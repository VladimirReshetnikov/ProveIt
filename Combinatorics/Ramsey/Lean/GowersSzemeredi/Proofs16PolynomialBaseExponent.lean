import GowersSzemeredi.Proofs16FreimanSliceProvider

/-! An explicit polynomial lower bound for the simultaneous base-case
width exponent. This replaces its logarithmic denominator by an elementary
bound and supplies a power of the loss for subsequent parameter estimates. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A coarse explicit polynomial estimate: the simultaneous base exponent
is at least `2^(-27) * sigma^3 / q^4`. -/
theorem polyBaseExponent_ge_cubic {q : Nat} {sigma : Real}
    (hq : 0 < q) (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    (2 : Real) ^ (-(27 : Real)) * sigma ^ 3 / (q : Real) ^ 4 ≤
      polyBaseExponent q sigma := by
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  have hη := polyBase_loss_pos hq hs
  have hT := polyBaseThreshold_ge_four hq hs hs1
  have hTpos : 0 < polyBaseThreshold q sigma := by linarith
  have hlog : 0 < Real.log (polyBaseThreshold q sigma) := Real.log_pos (by linarith)
  have hlogbound : Real.log (polyBaseThreshold q sigma) ≤ 4096 * (q : Real) / sigma := by
    calc
      Real.log (polyBaseThreshold q sigma) ≤ polyBaseThreshold q sigma :=
        (Real.log_le_sub_one_of_pos hTpos).trans (by linarith)
      _ ≤ 1024 * 4 / (sigma / (q : Real)) := by
        unfold polyBaseThreshold
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left Real.pi_lt_four.le (by norm_num)) hη.le
      _ = 4096 * (q : Real) / sigma := by field_simp; ring
  have hlog2 : (1 / 2 : Real) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at this ⊢
    exact this
  have ha := polyBaseCorExponent_pos hq hs
  unfold polyBaseExponent
  rw [le_div_iff₀ hlog]
  calc
    (2 : Real) ^ (-(27 : Real)) * sigma ^ 3 / (q : Real) ^ 4 *
        Real.log (polyBaseThreshold q sigma)
        ≤ (2 : Real) ^ (-(27 : Real)) * sigma ^ 3 / (q : Real) ^ 4 *
          (4096 * (q : Real) / sigma) :=
      mul_le_mul_of_nonneg_left hlogbound (by positivity)
    _ = polyBaseCorExponent q sigma * (1 / 2) := by
      unfold polyBaseCorExponent
      norm_num
      field_simp
      ring
    _ ≤ polyBaseCorExponent q sigma * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2 ha.le

end LeanProofs.GowersSzemeredi
