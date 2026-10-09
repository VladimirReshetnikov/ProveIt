import GowersSzemeredi.Proofs16GlobalAlmostAllTupleImages

/-! Quantitative readout of the prime-cyclic almost-all tuple construction.
The character rank is logarithmic in the number of classes, and the image
cap grows at most linearly in the reciprocal exceptional fraction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem clog_two_real_upper (M : Nat) :
    (Nat.clog 2 (M+1) : Real) ≤ 1+Real.log (M+1)/Real.log 2 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst M; norm_num
  have hr : 0 < Nat.clog 2 (M+1) := Nat.clog_pos (by norm_num) (by omega)
  have hp : (2 : Real)^(Nat.clog 2 (M+1)-1) < (M+1 : Real) := by
    exact_mod_cast (Nat.pow_pred_clog_lt_self (by norm_num : 1 < (2 : Nat)) (by omega : 1 < M+1))
  have hlog := Real.log_lt_log (by positivity) hp
  rw [Real.log_pow] at hlog
  have hcast : ((Nat.clog 2 (M+1)-1 : Nat) : Real) = (Nat.clog 2 (M+1) : Real)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast] at hlog
  have hl2 : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hupper := (le_div_iff₀ hl2).mpr hlog.le
  linarith

theorem globalColumnSparseKernelDensity_linear_epsilon (alpha epsilon : Real) (k r : Nat) :
    globalColumnSparseKernelDensity alpha k r epsilon =
      epsilon*globalColumnSparseKernelDensity alpha k r 1 := by
  unfold globalColumnSparseKernelDensity
  ring

/-- The image cap has at most reciprocal-linear dependence on epsilon. -/
theorem globalColumnAlmostAllTupleImageCap_scaled {alpha epsilon : Real}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    (globalColumnAlmostAllTupleImageCap alpha epsilon : Real) ≤
      ((globalColumnAlmostAllTupleImageCap alpha 1 : Real)+1)/epsilon := by
  have heta : 0 < globalColumnSparseKernelDensity alpha 15 1 1 :=
    globalColumnSparseKernelDensity_pos ha ha1 (by norm_num) 15 (by norm_num)
  have hcells : (0 : Real) < denseLevelCells (1/(4*Real.pi)) := by
    exact_mod_cast (Nat.ceil_pos.mpr (by positivity) : 0 < denseLevelCells (1/(4*Real.pi)))
  let x : Real := (denseLevelCells (1/(4*Real.pi)) : Real)^
    (16*columnSpectrumCap (columnEightDensity alpha))/globalColumnSparseKernelDensity alpha 15 1 1
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hcap : (globalColumnAlmostAllTupleImageCap alpha epsilon : Real) ≤ x/epsilon+1 := by
    unfold globalColumnAlmostAllTupleImageCap denseLevelImageCap
    rw [globalColumnSparseKernelDensity_linear_epsilon alpha epsilon 15 1]
    have heq : (denseLevelCells (1/(4*Real.pi)) : Real)^
        (16*columnSpectrumCap (columnEightDensity alpha))/
          (epsilon*globalColumnSparseKernelDensity alpha 15 1 1) = x/epsilon := by dsimp [x]; field_simp
    rw [heq]
    exact (Nat.ceil_lt_add_one (div_nonneg hx he.le)).le
  have hxcap : x ≤ (globalColumnAlmostAllTupleImageCap alpha 1 : Real) := Nat.le_ceil _
  calc
    _ ≤ x/epsilon+1 := hcap
    _ ≤ ((globalColumnAlmostAllTupleImageCap alpha 1 : Real)+1)/epsilon := by
      rw [le_div_iff₀ he]
      have hcancel : x/epsilon*epsilon = x := div_mul_cancel₀ x he.ne'
      nlinarith

/-- The rank certificate keeps the logarithm of the class budget. -/
theorem globalColumnTupleValueCharacterBudget_log (alpha : Real) :
    (globalColumnTupleValueCharacterBudget alpha : Real) ≤
      1+Real.log (globalColumnTupleValueModelCap alpha+1)/Real.log 2 :=
  clog_two_real_upper (globalColumnTupleValueModelCap alpha)

end LeanProofs.GowersSzemeredi
