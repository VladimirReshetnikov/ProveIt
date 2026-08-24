import IntegerPoints.IwaniecMozzochi

/-!
# Elementary scale bounds in Iwaniec--Mozzochi

This file proves the elementary scale consequences (6.3) and (6.6).  They use
the inequalities packaged in `InMainRange`, the exact value
`theta0 = 7 / 22`, and, for (6.3), the denominator bound from `InFareySet`.
-/

open Real

namespace LeanProofs.IntegerPoints

private theorem eq63_rpow_identity {x : ℝ} (hx : 0 < x) :
    (x ^ ((3 : ℝ) / 44) * x) *
        (x ^ (-(7 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22)) =
      x ^ ((19 : ℝ) / 44) := by
  have ha : x ^ ((3 : ℝ) / 44) * x = x ^ ((3 : ℝ) / 44 + 1) := by
    simpa using (Real.rpow_add hx ((3 : ℝ) / 44) 1).symm
  have hb : x ^ (-(7 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22) =
      x ^ (-(7 : ℝ) / 22 + -(7 : ℝ) / 22) :=
    (Real.rpow_add hx (-(7 : ℝ) / 22) (-(7 : ℝ) / 22)).symm
  have hc : x ^ ((3 : ℝ) / 44 + 1) *
      x ^ (-(7 : ℝ) / 22 + -(7 : ℝ) / 22) =
      x ^ (((3 : ℝ) / 44 + 1) +
        (-(7 : ℝ) / 22 + -(7 : ℝ) / 22)) :=
    (Real.rpow_add hx _ _).symm
  rw [ha, hb, hc]
  norm_num

/-- An assumption-minimal numeric form of the constant-one lower bound in
Iwaniec--Mozzochi (6.3).  It isolates the two scale comparisons used by the
argument from the `InMainRange` and `InFareySet` packaging. -/
theorem fareyLength_ge_rpow
    (x H M : ℝ) (c : ℕ)
    (hx : 0 < x) (hH : 0 < H) (hc : 0 < (c : ℝ))
    (hcH : (c : ℝ) ≤ H)
    (hHupper : H ≤ M * x ^ (-(7 : ℝ) / 22))
    (hMlower : x ^ ((19 : ℝ) / 44) ≤ M) :
    x ^ ((3 : ℝ) / 44) ≤ fareyLength x H M c := by
  have hB0 : 0 ≤ M * x ^ (-(7 : ℝ) / 22) := hH.le.trans hHupper
  have hcH' : (c : ℝ) * H ≤ H * H :=
    mul_le_mul_of_nonneg_right hcH hH.le
  have hHsq : H * H ≤
      (M * x ^ (-(7 : ℝ) / 22)) * (M * x ^ (-(7 : ℝ) / 22)) :=
    mul_le_mul hHupper hHupper hH.le hB0
  have hfactor0 : 0 ≤ x ^ ((3 : ℝ) / 44) * x :=
    mul_nonneg (Real.rpow_nonneg hx.le _) hx.le
  have hMtwo0 : 0 ≤ M ^ 2 := sq_nonneg M
  unfold fareyLength
  apply (le_div_iff₀ (mul_pos (mul_pos hx hc) hH)).2
  calc
    x ^ ((3 : ℝ) / 44) * (x * (c : ℝ) * H) =
        (x ^ ((3 : ℝ) / 44) * x) * ((c : ℝ) * H) := by ring
    _ ≤ (x ^ ((3 : ℝ) / 44) * x) * (H * H) :=
      mul_le_mul_of_nonneg_left hcH' hfactor0
    _ ≤ (x ^ ((3 : ℝ) / 44) * x) *
        ((M * x ^ (-(7 : ℝ) / 22)) * (M * x ^ (-(7 : ℝ) / 22))) :=
      mul_le_mul_of_nonneg_left hHsq hfactor0
    _ = ((x ^ ((3 : ℝ) / 44) * x) *
          (x ^ (-(7 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22))) * M ^ 2 := by
      ring
    _ = x ^ ((19 : ℝ) / 44) * M ^ 2 := by rw [eq63_rpow_identity hx]
    _ ≤ M * M ^ 2 := mul_le_mul_of_nonneg_right hMlower hMtwo0
    _ = M ^ 3 := by ring

/-- **Iwaniec--Mozzochi (6.3), second part.**  On the main range, the
representative scale `M^3 / (x c H)` is at least `x^(3/44)`.  Thus the
implicit absolute constant in this scale lower bound may be chosen to be
exactly one.  Comparing this proxy with the length of an actual Farey cell is
a separate geometric obligation. -/
theorem iwaniecMozzochi_eq63_holds : iwaniecMozzochi_eq63 := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro x H M a c hmain hfarey
  rcases hmain with ⟨hx, _, _, hH, hHupper, _, _, hMlower⟩
  rcases hfarey with ⟨hc, hcH, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hc0 : 0 < (c : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hc)
  simp only [one_mul]
  apply fareyLength_ge_rpow x H M c hx0 hH0 hc0 hcH
  · convert hHupper using 1
    norm_num [theta0]
  · calc
      x ^ ((19 : ℝ) / 44) = x ^ ((9 : ℝ) / 2 * theta0 - 1) := by
        congr 1
        norm_num [theta0]
      _ ≤ M := hMlower.le

/-- The paper's Weyl-shift scale has the normalized exponent `-3/11`. -/
theorem shiftLength_eq_mul_rpow {x M : ℝ} :
    shiftLength x M = M * x ^ (-(3 : ℝ) / 11) := by
  unfold shiftLength
  congr 1
  norm_num [theta0]

private theorem eq66_rpow_eight_elevenths {x : ℝ} (hx : 0 < x) :
    x * x ^ (-(3 : ℝ) / 11) = x ^ ((8 : ℝ) / 11) := by
  calc
    x * x ^ (-(3 : ℝ) / 11) =
        x ^ ((1 : ℝ) + -(3 : ℝ) / 11) := by
      simpa using (Real.rpow_add hx (1 : ℝ) (-(3 : ℝ) / 11)).symm
    _ = x ^ ((8 : ℝ) / 11) := by norm_num

private theorem eq66_rpow_nine_twenty_seconds {x : ℝ} (hx : 0 < x) :
    x ^ ((8 : ℝ) / 11) * x ^ (-(7 : ℝ) / 22) =
      x ^ ((9 : ℝ) / 22) := by
  calc
    x ^ ((8 : ℝ) / 11) * x ^ (-(7 : ℝ) / 22) =
        x ^ ((8 : ℝ) / 11 + -(7 : ℝ) / 22) :=
      (Real.rpow_add hx _ _).symm
    _ = x ^ ((9 : ℝ) / 22) := by norm_num

private theorem eq66_rpow_cancel {x : ℝ} (hx : 0 < x) :
    x ^ ((8 : ℝ) / 11) *
        (x ^ (-(4 : ℝ) / 11) * x ^ (-(4 : ℝ) / 11)) = 1 := by
  have hneg : x ^ (-(4 : ℝ) / 11) * x ^ (-(4 : ℝ) / 11) =
      x ^ (-(4 : ℝ) / 11 + -(4 : ℝ) / 11) :=
    (Real.rpow_add hx _ _).symm
  rw [hneg, ← Real.rpow_add hx]
  norm_num

/-- **Iwaniec--Mozzochi (6.6).**  For the shift length
`N = M x^(-3/11)` selected in (6.4), the scale `G = M³/(xNH)` lies in the
full claimed range `1 ≤ G ≤ H`. -/
theorem iwaniecMozzochi_eq66_holds : iwaniecMozzochi_eq66 := by
  intro x H M hmain
  rcases hmain with ⟨hx, hxM, _, hH, hHupper, hHlower, _, hMlower⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hHupper' : H ≤ M * x ^ (-(7 : ℝ) / 22) := by
    convert hHupper using 1
    norm_num [theta0]
  have hHlower' : M * x ^ (-(4 : ℝ) / 11) < H := by
    convert hHlower using 1
    norm_num [theta0]
  have hMlower' : x ^ ((19 : ℝ) / 44) < M := by
    convert hMlower using 1
    norm_num [theta0]
  have hx9_le_x19 : x ^ ((9 : ℝ) / 22) ≤ x ^ ((19 : ℝ) / 44) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hx9_le_M : x ^ ((9 : ℝ) / 22) ≤ M :=
    hx9_le_x19.trans hMlower'.le
  have hxneg3 : 0 < x ^ (-(3 : ℝ) / 11) := Real.rpow_pos_of_pos hx0 _
  have hxneg4 : 0 < x ^ (-(4 : ℝ) / 11) := Real.rpow_pos_of_pos hx0 _
  have hx8 : 0 < x ^ ((8 : ℝ) / 11) := Real.rpow_pos_of_pos hx0 _
  have hshift0 : 0 < M * x ^ (-(3 : ℝ) / 11) := mul_pos hM0 hxneg3
  have hden0 : 0 < x * (M * x ^ (-(3 : ℝ) / 11)) * H :=
    mul_pos (mul_pos hx0 hshift0) hH0
  constructor
  · unfold Gscale
    rw [shiftLength_eq_mul_rpow]
    apply (le_div_iff₀ hden0).2
    simp only [one_mul]
    have hprefix0 : 0 ≤ x * (M * x ^ (-(3 : ℝ) / 11)) :=
      (mul_pos hx0 hshift0).le
    have hMtwo0 : 0 ≤ M ^ 2 := sq_nonneg M
    calc
      x * (M * x ^ (-(3 : ℝ) / 11)) * H ≤
          x * (M * x ^ (-(3 : ℝ) / 11)) *
            (M * x ^ (-(7 : ℝ) / 22)) :=
        mul_le_mul_of_nonneg_left hHupper' hprefix0
      _ = M ^ 2 *
          ((x * x ^ (-(3 : ℝ) / 11)) * x ^ (-(7 : ℝ) / 22)) := by ring
      _ = M ^ 2 *
          (x ^ ((8 : ℝ) / 11) * x ^ (-(7 : ℝ) / 22)) := by
        rw [eq66_rpow_eight_elevenths hx0]
      _ = M ^ 2 * x ^ ((9 : ℝ) / 22) := by
        rw [eq66_rpow_nine_twenty_seconds hx0]
      _ ≤ M ^ 2 * M := mul_le_mul_of_nonneg_left hx9_le_M hMtwo0
      _ = M ^ 3 := by ring
  · unfold Gscale
    rw [shiftLength_eq_mul_rpow]
    apply (div_le_iff₀ hden0).2
    have hB0 : 0 ≤ M * x ^ (-(4 : ℝ) / 11) :=
      (mul_pos hM0 hxneg4).le
    have hHsq :
        (M * x ^ (-(4 : ℝ) / 11)) * (M * x ^ (-(4 : ℝ) / 11)) ≤ H * H :=
      mul_le_mul hHlower'.le hHlower'.le hB0 hH0.le
    have hfactor0 : 0 ≤ M * x ^ ((8 : ℝ) / 11) := (mul_pos hM0 hx8).le
    have hscaled := mul_le_mul_of_nonneg_left hHsq hfactor0
    have hleft :
        (M * x ^ ((8 : ℝ) / 11)) *
            ((M * x ^ (-(4 : ℝ) / 11)) * (M * x ^ (-(4 : ℝ) / 11))) =
          M ^ 3 := by
      calc
        (M * x ^ ((8 : ℝ) / 11)) *
            ((M * x ^ (-(4 : ℝ) / 11)) * (M * x ^ (-(4 : ℝ) / 11))) =
            M ^ 3 * (x ^ ((8 : ℝ) / 11) *
              (x ^ (-(4 : ℝ) / 11) * x ^ (-(4 : ℝ) / 11))) := by ring
        _ = M ^ 3 := by rw [eq66_rpow_cancel hx0, mul_one]
    calc
      M ^ 3 =
          (M * x ^ ((8 : ℝ) / 11)) *
            ((M * x ^ (-(4 : ℝ) / 11)) * (M * x ^ (-(4 : ℝ) / 11))) :=
        hleft.symm
      _ ≤ (M * x ^ ((8 : ℝ) / 11)) * (H * H) := hscaled
      _ = H * (x * (M * x ^ (-(3 : ℝ) / 11)) * H) := by
        rw [← eq66_rpow_eight_elevenths hx0]
        ring

end LeanProofs.IntegerPoints
