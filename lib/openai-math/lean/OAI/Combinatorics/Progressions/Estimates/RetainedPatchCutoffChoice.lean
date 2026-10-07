import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

noncomputable def retainedPatchCutoff (ε : ℝ) : ℕ := ⌈16 / ε⌉₊

noncomputable def retainedPatchRelativeError (ε : ℝ) : ℝ := ε / 4

theorem retainedPatchCutoffChoice_bounds {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    retainedPatchRelativeError ε ∈ Set.Icc (0 : ℝ) 1 ∧
    0 < retainedPatchCutoff ε ∧
    2 / (retainedPatchCutoff ε : ℝ) ≤ 1 / 2 ∧
    4 / (retainedPatchCutoff ε : ℝ) ≤ retainedPatchRelativeError ε ∧
    (1 + retainedPatchRelativeError ε) * (1 - ε) ≤ 1 - retainedPatchRelativeError ε ∧
    (retainedPatchCutoff ε : ℝ) ≤ 16 / ε + 1 ∧
    (retainedPatchCutoff ε : ℝ) ≤ 17 / ε := by
  have hlo : 16 / ε ≤ (retainedPatchCutoff ε : ℝ) := Nat.le_ceil _
  have hpos : 0 < retainedPatchCutoff ε := Nat.ceil_pos.mpr (by positivity)
  have hposr : (0 : ℝ) < retainedPatchCutoff ε := Nat.cast_pos.mpr hpos
  have hprod : 16 ≤ (retainedPatchCutoff ε : ℝ) * ε := (div_le_iff₀ hε).mp hlo
  have hsixteen : (16 : ℝ) ≤ retainedPatchCutoff ε :=
    ((le_div_iff₀ hε).mpr (by nlinarith)).trans hlo
  have hupp : (retainedPatchCutoff ε : ℝ) ≤ 16 / ε + 1 :=
    (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 16 / ε)).le
  refine ⟨⟨by unfold retainedPatchRelativeError; positivity,
    by unfold retainedPatchRelativeError; linarith⟩, hpos, ?_, ?_, ?_, hupp, ?_⟩
  · apply (div_le_iff₀ hposr).mpr
    linarith
  · apply (div_le_iff₀ hposr).mpr
    unfold retainedPatchRelativeError
    nlinarith only [hprod]
  · unfold retainedPatchRelativeError
    nlinarith [sq_nonneg ε]
  · apply hupp.trans
    apply (le_div_iff₀ hε).mpr
    have hcancel : (16 / ε : ℝ) * ε = 16 := div_mul_cancel₀ _ hε.ne'
    nlinarith only [hcancel, hεone]

private theorem seventeen_le_exp_four : (17 : ℝ) ≤ Real.exp 4 := by
  have hbase : (9 / 5 : ℝ) ≤ Real.exp (4 / 5) := by
    linarith only [Real.add_one_le_exp (4 / 5 : ℝ)]
  have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 5) hbase 5
  have hexp : (Real.exp (4 / 5 : ℝ)) ^ 5 = Real.exp 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hexp] at hpower
  norm_num at hpower
  linarith

theorem retainedPatchCutoff_le_exp {ε B : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hinv : ε⁻¹ ≤ Real.exp B) :
    (retainedPatchCutoff ε : ℝ) ≤ Real.exp (B + 4) := by
  have hcut := (retainedPatchCutoffChoice_bounds hε hεone).2.2.2.2.2.2
  calc
    _ ≤ 17 / ε := hcut
    _ = (17 : ℝ) * ε⁻¹ := div_eq_mul_inv _ _
    _ ≤ Real.exp 4 * Real.exp B :=
      mul_le_mul seventeen_le_exp_four hinv (inv_nonneg.mpr hε.le) (Real.exp_nonneg _)
    _ = Real.exp (B + 4) := by rw [← Real.exp_add, add_comm]

end Erdos3

end

end OAI
