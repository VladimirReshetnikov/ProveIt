import IntegerPoints.IwaniecMozzochi

/-!
# Elementary scale bounds in Iwaniec--Mozzochi

This file proves the elementary scale consequences of the main range.  The
first result, (6.3), only uses the inequalities packaged in `InMainRange` and
`InFareySet`, together with the exact value `theta0 = 7 / 22`.
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

/-- **Iwaniec--Mozzochi (6.3), second part.**  On the main range, every
Farey interval has length at least `x^(3/44)`.  Thus the implicit absolute
constant in the stated lower bound may be chosen to be exactly one. -/
theorem iwaniecMozzochi_eq63_holds : iwaniecMozzochi_eq63 := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro x H M a c hmain hfarey
  rcases hmain with ⟨hx, hxM, _, hH, hHupper, _, _, hMlower⟩
  rcases hfarey with ⟨hc, hcH, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hc0 : 0 < (c : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hc)
  have hHupper' : H ≤ M * x ^ (-(7 : ℝ) / 22) := by
    convert hHupper using 1
    norm_num [theta0]
  have hMlower' : x ^ ((19 : ℝ) / 44) < M := by
    convert hMlower using 1
    norm_num [theta0]
  have hxneg0 : 0 ≤ x ^ (-(7 : ℝ) / 22) :=
    (Real.rpow_pos_of_pos hx0 _).le
  have hB0 : 0 ≤ M * x ^ (-(7 : ℝ) / 22) := mul_nonneg hM0.le hxneg0
  have hcH' : (c : ℝ) * H ≤ H * H :=
    mul_le_mul_of_nonneg_right hcH hH0.le
  have hHsq : H * H ≤
      (M * x ^ (-(7 : ℝ) / 22)) * (M * x ^ (-(7 : ℝ) / 22)) :=
    mul_le_mul hHupper' hHupper' hH0.le hB0
  have hfactor0 : 0 ≤ x ^ ((3 : ℝ) / 44) * x :=
    mul_nonneg (Real.rpow_nonneg hx0.le _) hx0.le
  have hMtwo0 : 0 ≤ M ^ 2 := sq_nonneg M
  unfold fareyLength
  simp only [one_mul]
  apply (le_div_iff₀ (mul_pos (mul_pos hx0 hc0) hH0)).2
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
    _ = x ^ ((19 : ℝ) / 44) * M ^ 2 := by rw [eq63_rpow_identity hx0]
    _ ≤ M * M ^ 2 := mul_le_mul_of_nonneg_right hMlower'.le hMtwo0
    _ = M ^ 3 := by ring

end LeanProofs.IntegerPoints
