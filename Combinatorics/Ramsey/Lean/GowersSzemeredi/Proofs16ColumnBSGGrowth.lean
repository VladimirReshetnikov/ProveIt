import GowersSzemeredi.Proofs16GlobalColumnBSG

/-! The BSG route starts from a density that is only singly exponential.

`global_column_bsg` and `global_column_word_system` take
`γ = globalColumnQuadrupleDensity α` as their only density input, and every
loss after it is polynomial in `γ` and `α`. This module bounds `γ` from
below. Write `d = columnSpectrumCap (columnEightDensity α)`.
* `columnEightDensity_ge`: `β = columnEightDensity α` is a fixed power of
  `α/2` times `2^(-1882)`.
* `globalColumnQuadrupleDensity_ge`:
  `2^(-30121)·(α/2)^74500 / 13^(4d) ≤ γ` for `0 < α ≤ 1`.

So `log(1/γ) ≤ 4d·log 13 + O(log(1/α))`, a polynomial in `1/α`, since
`d ≤ 16/β² + 1`. The model-elimination core instead guaranteed only
`exp(-2^(13^d)/2)` (`globalColumnAgreementDensity_le_triple_exp`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem columnEightDensity_ge {alpha : Real} (ha : 0 < alpha) :
    (2 : Real) ^ (-(1882 : Real)) * (alpha / 2) ^ 4656 ≤ columnEightDensity alpha := by
  unfold columnEightDensity
  rw [← pow_mul]

/-- **The BSG route's density is singly exponential.** -/
theorem globalColumnQuadrupleDensity_ge {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    (2 : Real) ^ (-(30121 : Real)) * (alpha / 2) ^ 74500 /
        (13 : Real) ^ (4 * columnSpectrumCap (columnEightDensity alpha)) ≤
      globalColumnQuadrupleDensity alpha := by
  set β := columnEightDensity alpha with hβdef
  set d := columnSpectrumCap β with hddef
  have hβ0 : 0 < β := columnEightDensity_pos ha
  have hβ := columnEightDensity_ge ha
  rw [← hβdef] at hβ
  have hr : alpha / 2 ≤ alpha / (2 - alpha) :=
    div_le_div_of_nonneg_left ha.le (by linarith) (by linarith)
  have h13 : (0 : Real) < 13 ^ d := by positivity
  -- the witness density
  have hw : columnWitnessDensity β = β ^ 4 / (4 * 13 ^ d) := rfl
  unfold globalColumnQuadrupleDensity
  rw [← hβdef, hw]
  -- monotonicity in `β` and in `α/(2-α)`
  have hβ4 : ((2 : Real) ^ (-(1882 : Real)) * (alpha / 2) ^ 4656) ^ 16 ≤ β ^ 16 :=
    pow_le_pow_left₀ (by positivity) hβ 16
  have hr4 : (alpha / 2) ^ 4 ≤ (alpha / (2 - alpha)) ^ 4 := pow_le_pow_left₀ (by positivity) hr 4
  have hlhs : (2 : Real) ^ (-(30121 : Real)) * (alpha / 2) ^ 74500 / (13 : Real) ^ (4 * d) =
      ((2 : Real) ^ (-(1882 : Real)) * (alpha / 2) ^ 4656) ^ 16 * (alpha / 2) ^ 4 /
        (512 * ((13 : Real) ^ d) ^ 4) := by
    have h2 : (2 : Real) ^ (-(30121 : Real)) = ((2 : Real) ^ (-(1882 : Real))) ^ 16 / 512 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [show (512 : Real) = (2 : Real) ^ (9 : Real) by norm_num, ← Real.rpow_sub (by norm_num)]
      norm_num
    rw [h2, ← pow_mul]
    field_simp
    ring
  rw [hlhs]
  have hrhs : (β ^ 4 / (4 * 13 ^ d)) ^ 4 * (alpha / (2 - alpha)) ^ 4 / 2 =
      β ^ 16 * (alpha / (2 - alpha)) ^ 4 / (512 * ((13 : Real) ^ d) ^ 4) := by
    field_simp
    ring
  rw [hrhs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul hβ4 hr4 (by positivity) (by positivity)

end LeanProofs.GowersSzemeredi
