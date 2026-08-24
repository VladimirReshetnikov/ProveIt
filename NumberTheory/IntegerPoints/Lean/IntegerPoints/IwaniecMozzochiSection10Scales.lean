import IntegerPoints.IwaniecMozzochiRanges

/-!
# The section 10 scales in Iwaniec--Mozzochi

This file proves the scale comparisons (10.4) and (10.7).  In the notation of
the paper, `L = C / G` and `K / L = N / H`.  The main-range inequalities give
`x^(1/22) * H ≤ N ≤ x^(1/11) * H`, so all four implicit constants can be
chosen explicitly.
-/

open Real

namespace LeanProofs.IntegerPoints

private theorem eq104_rpow_lower {x : ℝ} (hx : 0 < x) :
    x ^ ((1 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22) =
      x ^ (-(3 : ℝ) / 11) := by
  calc
    x ^ ((1 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22) =
        x ^ ((1 : ℝ) / 22 + -(7 : ℝ) / 22) :=
      (Real.rpow_add hx _ _).symm
    _ = x ^ (-(3 : ℝ) / 11) := by norm_num

private theorem eq104_rpow_upper {x : ℝ} (hx : 0 < x) :
    x ^ ((1 : ℝ) / 11) * x ^ (-(4 : ℝ) / 11) =
      x ^ (-(3 : ℝ) / 11) := by
  calc
    x ^ ((1 : ℝ) / 11) * x ^ (-(4 : ℝ) / 11) =
        x ^ ((1 : ℝ) / 11 + -(4 : ℝ) / 11) :=
      (Real.rpow_add hx _ _).symm
    _ = x ^ (-(3 : ℝ) / 11) := by norm_num

private theorem eq104_Lscale_mul_Gscale {x C H M : ℝ}
    (hx : 0 < x) (hN : 0 < shiftLength x M) (hH : 0 < H) (hM : 0 < M) :
    Lscale x C H M * Gscale x H M = C := by
  unfold Lscale Gscale
  field_simp [hx.ne', hN.ne', hH.ne', hM.ne']

/-- **Iwaniec--Mozzochi (10.4) and (10.7).**  The four comparison constants
may be chosen as `mu1`, `1`, `1`, and `1`, respectively. -/
theorem iwaniecMozzochi_eq104_eq107_holds : iwaniecMozzochi_eq104_eq107 := by
  intro μ₁ hμ₁
  refine ⟨μ₁, 1, 1, 1, hμ₁, by norm_num, by norm_num, by norm_num, ?_⟩
  intro x C H M hmain hshort _hCH
  have hGbounds := iwaniecMozzochi_eq66_holds x H M hmain
  rcases hmain with ⟨hx, hxM, _, hH, hHupper, hHlower, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hxM
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hN0 : 0 < shiftLength x M := by
    rw [shiftLength_eq_mul_rpow]
    exact mul_pos hM0 (Real.rpow_pos_of_pos hx0 _)
  have hG1 : 1 ≤ Gscale x H M := hGbounds.1
  have hG0 : 0 < Gscale x H M := zero_lt_one.trans_le hG1
  have hC0 : 0 < C := (mul_pos hμ₁ hG0).trans hshort
  have hL0 : 0 < Lscale x C H M := by
    unfold Lscale
    positivity
  have hLG : Lscale x C H M * Gscale x H M = C :=
    eq104_Lscale_mul_Gscale hx0 hN0 hH0 hM0

  have hLlower : μ₁ ≤ Lscale x C H M := by
    refine le_of_lt (lt_of_mul_lt_mul_right ?_ hG0.le)
    calc
      μ₁ * Gscale x H M < C := hshort
      _ = Lscale x C H M * Gscale x H M := hLG.symm
  have hLupper : Lscale x C H M ≤ C := by
    calc
      Lscale x C H M = Lscale x C H M * 1 := by ring
      _ ≤ Lscale x C H M * Gscale x H M :=
        mul_le_mul_of_nonneg_left hG1 hL0.le
      _ = C := hLG

  have hHupper' : H ≤ M * x ^ (-(7 : ℝ) / 22) := by
    convert hHupper using 1
    norm_num [theta0]
  have hHlower' : M * x ^ (-(4 : ℝ) / 11) < H := by
    convert hHlower using 1
    norm_num [theta0]
  have hNlower : x ^ ((1 : ℝ) / 22) * H ≤ shiftLength x M := by
    rw [shiftLength_eq_mul_rpow]
    calc
      x ^ ((1 : ℝ) / 22) * H ≤
          x ^ ((1 : ℝ) / 22) * (M * x ^ (-(7 : ℝ) / 22)) :=
        mul_le_mul_of_nonneg_left hHupper' (Real.rpow_nonneg hx0.le _)
      _ = M *
          (x ^ ((1 : ℝ) / 22) * x ^ (-(7 : ℝ) / 22)) := by ring
      _ = M * x ^ (-(3 : ℝ) / 11) := by rw [eq104_rpow_lower hx0]
  have hNupper : shiftLength x M ≤ x ^ ((1 : ℝ) / 11) * H := by
    rw [shiftLength_eq_mul_rpow]
    calc
      M * x ^ (-(3 : ℝ) / 11) =
          M * (x ^ ((1 : ℝ) / 11) * x ^ (-(4 : ℝ) / 11)) := by
        rw [eq104_rpow_upper hx0]
      _ = x ^ ((1 : ℝ) / 11) *
          (M * x ^ (-(4 : ℝ) / 11)) := by ring
      _ ≤ x ^ ((1 : ℝ) / 11) * H :=
        mul_le_mul_of_nonneg_left hHlower'.le (Real.rpow_nonneg hx0.le _)

  let B := x * C * shiftLength x M / M ^ 3
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hLbase : Lscale x C H M = B * H := by
    dsimp [B]
    unfold Lscale
    ring
  have hKbase : Kscale x C M = B * shiftLength x M := by
    dsimp [B]
    unfold Kscale
    ring
  have hKlower :
      x ^ ((1 : ℝ) / 22) * Lscale x C H M ≤ Kscale x C M := by
    rw [hLbase, hKbase]
    calc
      x ^ ((1 : ℝ) / 22) * (B * H) =
          B * (x ^ ((1 : ℝ) / 22) * H) := by ring
      _ ≤ B * shiftLength x M := mul_le_mul_of_nonneg_left hNlower hB0
  have hKupper :
      Kscale x C M ≤ x ^ ((1 : ℝ) / 11) * Lscale x C H M := by
    rw [hLbase, hKbase]
    calc
      B * shiftLength x M ≤ B * (x ^ ((1 : ℝ) / 11) * H) :=
        mul_le_mul_of_nonneg_left hNupper hB0
      _ = x ^ ((1 : ℝ) / 11) * (B * H) := by ring

  exact ⟨hLlower, by simpa using hLupper, by simpa using hKlower,
    by simpa using hKupper⟩

end LeanProofs.IntegerPoints
