import GowersSzemeredi.Proofs16Slicing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Quantitative inversion of phase distance on the cyclic group. Jordan's
inequality gives the centered modular distance from the chord length. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

alias exponential_eq_exp_valMinAbs := cor57_exponential_eq_exp_valMinAbs

theorem four_centeredAbs_div_le_phase_norm {N : Nat} [NeZero N] (x : ZMod N) :
    4 * (centeredAbs x : Real) / N ≤ ‖exponential x - 1‖ := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have habs : |Real.pi * (x.valMinAbs : Real) / N| = Real.pi * centeredAbs x / N := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hN, centeredAbs, Nat.cast_natAbs,
      Int.cast_abs]
  have hcenter : (centeredAbs x : Real) * 2 ≤ N := by
    exact_mod_cast (Nat.mul_le_mul_right 2 (ZMod.natAbs_valMinAbs_le x)).trans
      (Nat.div_mul_le_self N 2)
  -- Jordan's inequality at `t = π v / N`, where `|t| ≤ π / 2`
  have hs := Real.mul_abs_le_abs_sin
    (show |Real.pi * (x.valMinAbs : Real) / N| ≤ Real.pi / 2 by
      rw [habs, div_le_iff₀ hN]
      linarith [mul_le_mul_of_nonneg_left hcenter Real.pi_pos.le])
  rw [habs] at hs
  rw [exponential_eq_exp_valMinAbs, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_two, show 2 * Real.pi * (x.valMinAbs : Real) / N / 2 =
      Real.pi * x.valMinAbs / N by ring]
  calc _ = 2 * (2 / Real.pi * (Real.pi * centeredAbs x / N)) := by field_simp; ring
    _ ≤ _ := by gcongr

theorem phase_norm_sub_eq {N : Nat} [NeZero N] (x y : ZMod N) :
    ‖exponential x - exponential y‖ = ‖exponential (x - y) - 1‖ := by
  have hid : exponential x - exponential y = (exponential (x - y) - 1) * exponential y := by
    simp only [exponential]
    rw [sub_mul, one_mul, ← AddChar.map_add_eq_mul]
    simp only [sub_add_cancel]
  rw [hid, norm_mul]
  simp only [exponential, AddChar.norm_apply (ZMod.stdAddChar (N := N)), mul_one]

theorem centeredAbs_sub_le_phase_distance {N : Nat} [NeZero N] (x y : ZMod N) :
    (centeredAbs (x - y) : Real) ≤ (N : Real) / 4 * ‖exponential (-x) - exponential (-y)‖ := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have h := four_centeredAbs_div_le_phase_norm ((-x) - (-y))
  rw [show (-x) - (-y) = -(x - y) by ring, centeredAbs_neg] at h
  rw [phase_norm_sub_eq, show (-x) - (-y) = -(x - y) by ring]
  have ht := (div_le_iff₀ hN).mp h
  linarith only [ht]

theorem centeredAbs_sub_le_of_phase_cluster {N : Nat} [NeZero N]
    (x y : ZMod N) (z : Complex) {eta : Real}
    (hx : ‖exponential (-x) - z‖ ≤ eta) (hy : ‖exponential (-y) - z‖ ≤ eta) :
    (centeredAbs (x - y) : Real) ≤ (N : Real) * eta / 2 := by
  have hd := norm_sub_le_norm_sub_add_norm_sub (exponential (-x)) z (exponential (-y))
  rw [norm_sub_rev z] at hd
  have hdist : ‖exponential (-x) - exponential (-y)‖ ≤ 2 * eta := by linarith only [hd, hx, hy]
  calc
    _ ≤ (N : Real) / 4 * ‖exponential (-x) - exponential (-y)‖ := centeredAbs_sub_le_phase_distance x y
    _ ≤ (N : Real) / 4 * (2 * eta) := mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = _ := by ring

end LeanProofs.GowersSzemeredi
