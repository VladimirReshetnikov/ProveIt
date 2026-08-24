import IntegerPoints.IwaniecMozzochiRanges

/-!
# Iwaniec--Mozzochi: elementary foundations for (6.9)

This module collects the scale facts needed before constructing the Farey-cell
decomposition in (6.9).  It deliberately depends only on the elementary range
module: no convolution, Farey geometry, or Section 7 analytic estimate enters
these results.

The final identity is the exact version of the scale relation
`lambda / N = G / c` used in (6.7).
-/

open Real

namespace LeanProofs.IntegerPoints

/-- On the main range, the selected Weyl-shift length is at least one. -/
theorem mainRange_one_le_shiftLength
    {x H M : ℝ} (hmain : InMainRange x H M) :
    1 ≤ shiftLength x M := by
  rcases hmain with
    ⟨hx, hxM, _hMsqrt, hH, hHupper, _hHlower, _hHlowerTwo, _hMlower⟩
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hMnonneg : 0 ≤ M :=
    ((Real.rpow_pos_of_pos hxPos theta0).trans hxM).le
  have hrpow : x ^ (-theta0) ≤ x ^ (-(3 : ℝ) / 11) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num [theta0])
  calc
    1 ≤ H := hH
    _ ≤ M * x ^ (-theta0) := hHupper
    _ ≤ M * x ^ (-(3 : ℝ) / 11) :=
      mul_le_mul_of_nonneg_left hrpow hMnonneg
    _ = shiftLength x M := shiftLength_eq_mul_rpow.symm

/-- In particular, the selected Weyl-shift length is positive on the main
range. -/
theorem mainRange_shiftLength_pos
    {x H M : ℝ} (hmain : InMainRange x H M) :
    0 < shiftLength x M :=
  zero_lt_one.trans_le (mainRange_one_le_shiftLength hmain)

/-- The elementary bounds (6.6), exposed under a name convenient for the
global (6.9) reduction. -/
theorem mainRange_Gscale_bounds
    {x H M : ℝ} (hmain : InMainRange x H M) :
    1 ≤ Gscale x H M ∧ Gscale x H M ≤ H :=
  iwaniecMozzochi_eq66_holds x H M hmain

/-- In particular, the Farey scale `G` is positive on the main range. -/
theorem mainRange_Gscale_pos
    {x H M : ℝ} (hmain : InMainRange x H M) :
    0 < Gscale x H M :=
  zero_lt_one.trans_le (mainRange_Gscale_bounds hmain).1

/-- Exact scale identity behind (6.7):
`M³ / (x c H) = N * G / c`, with `N = shiftLength x M`.

Only positivity of the four denominator factors is used. -/
theorem fareyLength_eq_shiftLength_mul_Gscale_div
    {x H M : ℝ} {c : ℕ}
    (hx : 0 < x) (hH : 0 < H)
    (hN : 0 < shiftLength x M) (hc : 0 < c) :
    fareyLength x H M c =
      shiftLength x M * Gscale x H M / (c : ℝ) := by
  have hcReal : (0 : ℝ) < c := by exact_mod_cast hc
  unfold fareyLength Gscale
  field_simp [hx.ne', hH.ne', hN.ne', hcReal.ne']

/-- Main-range specialization of the exact scale identity (6.7). -/
theorem mainRange_fareyLength_eq_shiftLength_mul_Gscale_div
    {x H M : ℝ} {c : ℕ}
    (hmain : InMainRange x H M) (hc : 0 < c) :
    fareyLength x H M c =
      shiftLength x M * Gscale x H M / (c : ℝ) := by
  exact fareyLength_eq_shiftLength_mul_Gscale_div
    (zero_lt_one.trans_le hmain.1)
    (zero_lt_one.trans_le hmain.2.2.2.1)
    (mainRange_shiftLength_pos hmain) hc

end LeanProofs.IntegerPoints
