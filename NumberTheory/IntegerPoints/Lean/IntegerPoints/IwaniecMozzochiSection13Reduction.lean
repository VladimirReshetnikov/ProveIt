import IntegerPoints.IwaniecMozzochiSection12Scales

/-!
# Iwaniec--Mozzochi: the final Section 13 reduction

This module performs the last elementary implication in Section 13.  Once the
analytic reduction (12.4) and the uniform bound for its full 72-block
bilinear-form aggregate `section12BigB` are available, the desired estimate
for `deltaCHM` follows by adding the lower-order remainder.

The unconditional scale identity proved for (12.5) says that the remainder
scale is *exactly* `x^(13/44)`.  Since `13/44 < theta0 = 7/22`, it is
absorbed by `x^(theta0 + epsilon)` for `x >= 1`.  Equation (12.4) supplies its
own positive constant, independently of that identity.

The theorem below is deliberately conditional on the two substantive
analytic inputs.  It proves their bookkeeping implication; it does not claim
either input independently.
-/

namespace LeanProofs.IntegerPoints

/-- Equation (12.4) and the aggregate Section 13 bilinear-form estimate imply
the final `deltaCHM` bound.  The exact identity (12.5) is already unconditional
and is consumed directly rather than passed as an additional hypothesis. -/
theorem iwaniecMozzochi_section13_deltaCHMBound_of_eq124_of_bigBBound
    (h124 : iwaniecMozzochi_eq124)
    (hbigB : iwaniecMozzochi_section13_bigBBound) :
    iwaniecMozzochi_section13_deltaCHMBound := by
  intro chi sigma muOne epsilon hchi hsigma hmuOne hepsilon
  obtain ⟨A, hApos, hA⟩ := h124 chi sigma muOne hchi hsigma hmuOne
  obtain ⟨B, hB⟩ := hbigB muOne epsilon hmuOne hepsilon
  let Bpos : ℝ := max B 0
  refine ⟨A * (Bpos + 1), ?_⟩
  intro x C H M hmain hClower hCupper
  obtain ⟨tOne, tTwo, hdelta⟩ := hA x C H M hmain hClower hCupper

  have hx : 1 ≤ x := hmain.1
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hscale := iwaniecMozzochi_eq125_scale_identity hmain

  have hbigRaw :=
    hB x C H M tOne tTwo hmain hClower hCupper
  have hbigNormalized :
      section12BigB x (Gscale x H M) (Ascale x C M) C
          (Kscale x C M) (Lscale x C H M) tOne tTwo ≤
        Bpos * x ^ (theta0 + epsilon) := by
    exact hbigRaw.trans <|
      mul_le_mul_of_nonneg_right (show B ≤ Bpos by simp [Bpos])
        (Real.rpow_nonneg hx0.le _)

  have hexponent : (13 : ℝ) / 44 ≤ theta0 + epsilon := by
    norm_num [theta0]
    linarith
  have hsmallPower :
      x ^ ((13 : ℝ) / 44) ≤ x ^ (theta0 + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hx hexponent
  have hremainder :
      Gscale x H M * H * M ^ (-(2 : ℝ)) * x ^ ((45 : ℝ) / 44) ≤
        x ^ (theta0 + epsilon) := by
    rw [hscale]
    exact hsmallPower

  have hsum :
      section12BigB x (Gscale x H M) (Ascale x C M) C
          (Kscale x C M) (Lscale x C H M) tOne tTwo +
          Gscale x H M * H * M ^ (-(2 : ℝ)) * x ^ ((45 : ℝ) / 44) ≤
        (Bpos + 1) * x ^ (theta0 + epsilon) := by
    calc
      section12BigB x (Gscale x H M) (Ascale x C M) C
            (Kscale x C M) (Lscale x C H M) tOne tTwo +
            Gscale x H M * H * M ^ (-(2 : ℝ)) * x ^ ((45 : ℝ) / 44) ≤
          Bpos * x ^ (theta0 + epsilon) +
            x ^ (theta0 + epsilon) :=
        add_le_add hbigNormalized hremainder
      _ = (Bpos + 1) * x ^ (theta0 + epsilon) := by ring

  exact hdelta.trans <| by
    calc
      A * (section12BigB x (Gscale x H M) (Ascale x C M) C
            (Kscale x C M) (Lscale x C H M) tOne tTwo +
          Gscale x H M * H * M ^ (-(2 : ℝ)) * x ^ ((45 : ℝ) / 44)) ≤
          A * ((Bpos + 1) * x ^ (theta0 + epsilon)) :=
        mul_le_mul_of_nonneg_left hsum hApos.le
      _ = (A * (Bpos + 1)) * x ^ (theta0 + epsilon) := by ring

end LeanProofs.IntegerPoints
