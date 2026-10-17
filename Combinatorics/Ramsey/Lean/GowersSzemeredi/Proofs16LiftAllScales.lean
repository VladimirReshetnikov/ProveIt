import GowersSzemeredi.Proofs16LiftWidth
import GowersSzemeredi.Proofs16BaseCaseUnion

/-! # The verified local affine lift at every input scale

`section16_local_affine_lift_all_scales` is in `Proofs16LiftAllScalesSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_slice_control_ranges {r k : Nat} {s gamma ε : ℝ}
    (hr : 0 < r) (hs : 1 ≤ s) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < (multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ∧
    (multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ≤ 1 ∧
    1 ≤ (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ht : 1 ≤ (r : ℝ) * s := one_le_mul_of_one_le_of_one_le hr1 hs
  have ht0 : 0 < (r : ℝ) * s := zero_lt_one.trans_le ht
  have hi : ((r : ℝ) * s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  have hb : 0 < gamma * (((r : ℝ) * s)⁻¹ * ε) := by positivity
  have hb1 : gamma * (((r : ℝ) * s)⁻¹ * ε) ≤ 1 := by
    calc
      _ ≤ 1 * (1 * 1) := mul_le_mul hg1 (mul_le_mul hi hε1 hε.le (by norm_num))
        (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hc : 0 < multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k := pow_pos hb _
  have hc1 : multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k ≤ 1 := pow_le_one₀ hb.le hb1
  have hQ : 1 ≤ multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k := (one_le_inv₀ hc).mpr hc1
  exact ⟨Real.rpow_pos_of_pos hc _, Real.rpow_le_one hc.le hc1 ht0.le,
    Real.one_le_rpow hQ ht0.le⟩

alias isMultilinear_constant := BaseCase.isMultilinear_const

end LeanProofs.GowersSzemeredi
