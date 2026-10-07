import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem log_two_add_le_of_le_exp {x P : ℝ} (hx : 0 ≤ x) (hP : 0 ≤ P)
    (hbound : x ≤ Real.exp P) : Real.log (2 + x) ≤ P + 2 := by
  have he : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hh : 2 + x ≤ Real.exp (P + 2) := by
    rw [Real.exp_add]
    calc
      2 + x ≤ 3 * Real.exp P := by linarith
      _ ≤ Real.exp P * Real.exp 2 := by nlinarith [Real.exp_pos P]
  exact (Real.log_le_log (by positivity) hh).trans_eq (Real.log_exp _)

theorem baseline_scale_inv_le {v τ : ℝ} (hv : 0 ≤ v) (hτ : 0 < τ) :
    (2 * (v + τ))⁻¹ ≤ τ⁻¹ := by
  simpa only [one_div] using one_div_le_one_div_of_le hτ (by linarith : τ ≤ 2 * (v + τ))

theorem weighted_scale_inv_le {v τ level : ℝ} (hv : 0 ≤ v) (hτ : 0 < τ) (hl : 0 < level) :
    (4 * level * (v + τ))⁻¹ ≤ level⁻¹ * τ⁻¹ := by
  have h := one_div_le_one_div_of_le (mul_pos hl hτ)
    (show level * τ ≤ 4 * level * (v + τ) by nlinarith)
  simpa only [one_div, mul_inv_rev, mul_comm] using h

theorem site_normalization_caps {v τ level L T : ℝ}
    (hv : 0 ≤ v) (hτ : 0 < τ) (hl : 0 < level) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hlevel : Real.exp (-L) ≤ level) (hτinv : τ⁻¹ ≤ Real.exp T) :
    0 < 2 * (v + τ) ∧ 0 < 4 * level * (v + τ) ∧
    (2 * (v + τ))⁻¹ ≤ Real.exp (L + T) ∧
    (4 * level * (v + τ))⁻¹ ≤ Real.exp (L + T) ∧
    Real.log (2 + Real.exp (L + T)) ≤ L + T + 2 := by
  have hlinv : level⁻¹ ≤ Real.exp L := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (-L)) hlevel
    simpa only [one_div, Real.exp_neg, inv_inv] using hh
  have hbase : (2 * (v + τ))⁻¹ ≤ Real.exp (L + T) :=
    (baseline_scale_inv_le hv hτ).trans (hτinv.trans (Real.exp_le_exp.mpr (by linarith)))
  have hweighted : (4 * level * (v + τ))⁻¹ ≤ Real.exp (L + T) := by
    rw [Real.exp_add]
    exact (weighted_scale_inv_le hv hτ hl).trans
      (mul_le_mul hlinv hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos L).le)
  exact ⟨by positivity, by positivity, hbase, hweighted,
    log_two_add_le_of_le_exp (Real.exp_pos _).le (add_nonneg hL hT) le_rfl⟩

end Erdos3

end

end OAI
