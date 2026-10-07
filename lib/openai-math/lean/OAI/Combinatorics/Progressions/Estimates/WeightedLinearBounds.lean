import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open Module

theorem weighted_linear_bound_of_unit {E F ι κ : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (e : Basis ι ℝ E) (f : Basis κ ℝ F) (W : ι → ℝ) (V : κ → ℝ)
    (Φ : E →ₗ[ℝ] F) (C : ℝ)
    (hΦ : ∀ x, (∀ i, |e.repr x i| ≤ 1 / W i) → ∀ j, |f.repr (Φ x) j| ≤ C / V j)
    {M : ℝ} (hM : 0 ≤ M) (x : E) (hx : ∀ i, |e.repr x i| ≤ M / W i) :
    ∀ j, |f.repr (Φ x) j| ≤ C * M / V j := by
  by_cases hzero : M = 0
  · have hxi : x = 0 := by
      apply e.repr.injective
      ext i
      have hi : |e.repr x i| ≤ 0 := by simpa only [hzero, zero_div] using hx i
      simpa only [map_zero, Finsupp.zero_apply] using (abs_nonpos_iff.mp hi)
    intro j
    simp only [hxi, map_zero, Finsupp.zero_apply, abs_zero, hzero, mul_zero, zero_div, le_refl]
  · have hpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    let y : E := M⁻¹ • x
    have hy : ∀ i, |e.repr y i| ≤ 1 / W i := by
      intro i
      change |e.repr (M⁻¹ • x) i| ≤ _
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
      calc
        _ ≤ M⁻¹ * (M / W i) := mul_le_mul_of_nonneg_left (hx i) (inv_pos.mpr hpos).le
        _ = _ := by field_simp
    have hxy : x = M • y := by simp only [y, smul_smul, mul_inv_cancel₀ hzero, one_smul]
    intro j
    rw [hxy, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hpos]
    calc
      _ ≤ M * (C / V j) := mul_le_mul_of_nonneg_left (hΦ y hy j) hM
      _ = _ := by ring

end Erdos3

end

end OAI
