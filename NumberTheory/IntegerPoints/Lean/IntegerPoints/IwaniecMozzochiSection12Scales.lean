import IntegerPoints.IwaniecMozzochi

/-!
# The section 12 remainder scale in Iwaniec--Mozzochi

This file isolates the elementary part of (12.5) from the analytic estimate
in (12.4).  With `theta0 = 7 / 22`, the selected shift length is exactly
`N = M x^(-3/11)`.  Consequently the remainder scale occurring in (12.4)
simplifies without any loss:

`G H M^(-2) x^(45/44) = x^(13/44)`.

This is now the separate proposition `iwaniecMozzochi_eq125`; the substantive
analytic reduction `iwaniecMozzochi_eq124` has its own constant and is
deliberately not asserted here.
-/

open Real

namespace LeanProofs.IntegerPoints

private theorem eq125_shiftLength_eq (x M : ℝ) :
    shiftLength x M = M * x ^ (-(3 : ℝ) / 11) := by
  unfold shiftLength
  congr 1
  norm_num [theta0]

private theorem eq125_rpow_three_mul_neg_two {M : ℝ} (hM : 0 < M) :
    M ^ 3 * M ^ (-(2 : ℝ)) = M := by
  rw [← Real.rpow_natCast]
  calc
    M ^ (3 : ℝ) * M ^ (-(2 : ℝ)) =
        M ^ ((3 : ℝ) + -(2 : ℝ)) :=
      (Real.rpow_add hM _ _).symm
    _ = M := by norm_num [Real.rpow_one]

private theorem eq125_rpow_exponents {x : ℝ} (hx : 0 < x) :
    (x * x ^ (-(3 : ℝ) / 11)) * x ^ ((13 : ℝ) / 44) =
      x ^ ((45 : ℝ) / 44) := by
  calc
    (x * x ^ (-(3 : ℝ) / 11)) * x ^ ((13 : ℝ) / 44) =
        (x ^ (1 : ℝ) * x ^ (-(3 : ℝ) / 11)) *
          x ^ ((13 : ℝ) / 44) := by rw [Real.rpow_one]
    _ = x ^ ((1 : ℝ) + -(3 : ℝ) / 11) *
          x ^ ((13 : ℝ) / 44) := by
      rw [← Real.rpow_add hx]
    _ = x ^ (((1 : ℝ) + -(3 : ℝ) / 11) + (13 : ℝ) / 44) := by
      rw [← Real.rpow_add hx]
    _ = x ^ ((45 : ℝ) / 44) := by norm_num

/-- The exact scale identity under its minimal positivity assumptions. -/
theorem iwaniecMozzochi_eq125_scale_identity_of_pos {x H M : ℝ}
    (hx0 : 0 < x) (hH0 : 0 < H) (hM0 : 0 < M) :
    Gscale x H M * H * M ^ (-(2 : ℝ)) * x ^ ((45 : ℝ) / 44) =
      x ^ ((13 : ℝ) / 44) := by
  have hxNeg0 : 0 < x ^ (-(3 : ℝ) / 11) := Real.rpow_pos_of_pos hx0 _
  unfold Gscale
  rw [eq125_shiftLength_eq]
  calc
    M ^ 3 / (x * (M * x ^ (-(3 : ℝ) / 11)) * H) * H *
          M ^ (-(2 : ℝ)) * x ^ ((45 : ℝ) / 44) =
        (M ^ 3 * M ^ (-(2 : ℝ))) * x ^ ((45 : ℝ) / 44) /
          (x * M * x ^ (-(3 : ℝ) / 11)) := by
      field_simp [hx0.ne', hM0.ne', hH0.ne', hxNeg0.ne']
    _ = M * x ^ ((45 : ℝ) / 44) /
          (x * M * x ^ (-(3 : ℝ) / 11)) := by
      rw [eq125_rpow_three_mul_neg_two hM0]
    _ = x ^ ((45 : ℝ) / 44) /
          (x * x ^ (-(3 : ℝ) / 11)) := by
      field_simp [hx0.ne', hM0.ne', hxNeg0.ne']
    _ = x ^ ((13 : ℝ) / 44) := by
      apply (div_eq_iff (mul_ne_zero hx0.ne' hxNeg0.ne')).2
      calc
        x ^ ((45 : ℝ) / 44) =
            (x * x ^ (-(3 : ℝ) / 11)) * x ^ ((13 : ℝ) / 44) :=
          (eq125_rpow_exponents hx0).symm
        _ = x ^ ((13 : ℝ) / 44) *
            (x * x ^ (-(3 : ℝ) / 11)) := by ring

/-- **Iwaniec--Mozzochi (12.5), exact scale identity.**  On the main range,
the ostensibly lower-order term in (12.4) is exactly `x^(13/44)`, rather than
merely comparable to it. -/
theorem iwaniecMozzochi_eq125_scale_identity {x H M : ℝ}
    (hmain : InMainRange x H M) :
    Gscale x H M * H * M ^ (-(2 : ℝ)) * x ^ ((45 : ℝ) / 44) =
      x ^ ((13 : ℝ) / 44) := by
  rcases hmain with ⟨hx, hxM, _, hH, _, _, _, _⟩
  exact iwaniecMozzochi_eq125_scale_identity_of_pos
    (zero_lt_one.trans_le hx)
    (zero_lt_one.trans_le hH)
    ((Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) theta0).trans hxM)

/-- Equation (12.5) in its catalogue form. -/
theorem iwaniecMozzochi_eq125_holds : iwaniecMozzochi_eq125 := by
  intro x H M hmain
  exact iwaniecMozzochi_eq125_scale_identity hmain

end LeanProofs.IntegerPoints
