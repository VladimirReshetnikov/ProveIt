import GowersSzemeredi.Proofs16Slicing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Quantitative inversion of phase distance on the cyclic group. Jordan's
inequality gives the centered modular distance from the chord length. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem exponential_eq_exp_valMinAbs {N : Nat} [NeZero N] (x : ZMod N) :
    exponential x = Complex.exp
      (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) := by
  calc
    exponential x = ZMod.stdAddChar ((x.valMinAbs : Int) : ZMod N) := by simp [exponential]
    _ = Complex.exp (2 * Real.pi * Complex.I * (x.valMinAbs : Int) / N) :=
      ZMod.stdAddChar_coe x.valMinAbs
    _ = _ := by congr 1; push_cast; ring

theorem four_centeredAbs_div_le_phase_norm {N : Nat} [NeZero N] (x : ZMod N) :
    4 * (centeredAbs x : Real) / N ≤ ‖exponential x - 1‖ := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have habs : |(x.valMinAbs : Real)| = (centeredAbs x : Real) := by
    rw [centeredAbs, ← Int.cast_abs, Int.abs_eq_natAbs]
    rfl
  let t : Real := Real.pi * (x.valMinAbs : Real) / N
  have habst : |t| = Real.pi * centeredAbs x / N := by
    dsimp [t]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hN, habs]
  have hcenter : 2 * (centeredAbs x : Real) ≤ N := by
    have h := (Nat.mul_le_mul_right 2 (ZMod.natAbs_valMinAbs_le x)).trans (Nat.div_mul_le_self N 2)
    have hc : (centeredAbs x : Real) * 2 ≤ N := by exact_mod_cast h
    linarith only [hc]
  have ht : |t| ≤ Real.pi / 2 := by
    rw [habst]
    apply (div_le_iff₀ hN).mpr
    have h := mul_le_mul_of_nonneg_left hcenter Real.pi_pos.le
    linarith only [h]
  have hs := Real.mul_abs_le_abs_sin ht
  have hnorm : ‖exponential x - 1‖ = 2 * |Real.sin t| := by
    rw [exponential_eq_exp_valMinAbs, Complex.norm_exp_I_mul_ofReal_sub_one]
    have heq : (2 * Real.pi * (x.valMinAbs : Real) / N) / 2 = t := by dsimp [t]; ring
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
  rw [hnorm]
  calc
    _ = 2 * (2 / Real.pi * |t|) := by rw [habst]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num)

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
