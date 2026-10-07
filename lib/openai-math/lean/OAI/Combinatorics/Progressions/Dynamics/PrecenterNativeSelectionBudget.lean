import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

section

namespace Erdos3.VectorPolynomial

private theorem precenter_exp_add_le_div (q a : ℝ) (ha : 0 < a)
    (hlog : Real.log a ≤ a) :
    Real.exp (-(q + a)) ≤ Real.exp (-q) / a := by
  calc
    _ ≤ Real.exp (-q - Real.log a) := Real.exp_le_exp.mpr (by linarith only [hlog])
    _ = _ := by rw [Real.exp_sub, Real.exp_log ha]

theorem precenter_native_selection_mass_budget
    {Bin : Type*} [Fintype Bin] [Nonempty Bin] (rank : ℕ)
    {b t d mass : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hrank : (rank : ℝ) ≤ d)
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp b) (hmass : 0 ≤ mass) :
    Real.exp (-(d * (b + t))) * mass ≤
      mass / ((Fintype.card Bin : ℝ) ^ rank * (Real.exp t) ^ rank) := by
  have hcardpos : (0 : ℝ) < Fintype.card Bin := by
    exact_mod_cast Fintype.card_pos
  have hden : 0 < (Fintype.card Bin : ℝ) ^ rank * (Real.exp t) ^ rank := by positivity
  have hbound : (Fintype.card Bin : ℝ) ^ rank * (Real.exp t) ^ rank ≤
      Real.exp (d * (b + t)) := by
    calc
      _ ≤ (Real.exp b) ^ rank * (Real.exp t) ^ rank :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hcardpos.le hcard rank) (by positivity)
      _ = Real.exp ((rank : ℝ) * (b + t)) := by
        rw [← mul_pow, ← Real.exp_add, Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrank (add_nonneg hb ht))
  calc
    _ = mass / Real.exp (d * (b + t)) := by rw [Real.exp_neg]; ring
    _ ≤ _ := div_le_div_of_nonneg_left hmass hden hbound

theorem precenter_native_selection_correlation_budget
    {Bin : Type*} [Fintype Bin] [Nonempty Bin] {rFreq b c : ℝ}
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp b) :
    Real.exp (-(rFreq + b + c + 4)) ≤
      (Real.exp (-rFreq) / (2 * (Fintype.card Bin : ℝ))) / (2 * Real.exp c) := by
  have hcardpos : (0 : ℝ) < Fintype.card Bin := by
    exact_mod_cast Fintype.card_pos
  have hfour : Real.log (4 : ℝ) ≤ 4 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)).trans (by norm_num)
  calc
    _ ≤ Real.exp (-(rFreq + b + c)) / 4 :=
      precenter_exp_add_le_div (rFreq + b + c) 4 (by norm_num) hfour
    _ = (Real.exp (-rFreq) / (2 * Real.exp b)) / (2 * Real.exp c) := by
      rw [show -(rFreq + b + c) = -rFreq - b - c by ring,
        Real.exp_sub, Real.exp_sub]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
        (mul_le_mul_of_nonneg_left hcard (by norm_num))) (by positivity)

theorem precenter_native_selection_residual_budget
    {Bin : Type*} [Fintype Bin] [Nonempty Bin] {pLocal Eres rFreq b : ℝ}
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp b)
    (hres : pLocal + rFreq + b + 4 ≤ Eres) :
    Real.exp (pLocal - Eres) ≤
      (Real.exp (-rFreq) / (2 * (Fintype.card Bin : ℝ))) / 2 := by
  calc
    _ ≤ Real.exp (-(rFreq + b + 0 + 4)) := Real.exp_le_exp.mpr (by linarith only [hres])
    _ ≤ _ := by simpa using (precenter_native_selection_correlation_budget (c := 0) hcard)

theorem precenter_native_selection_model_error_budget (inputLog rFreq : ℝ) :
    Real.exp inputLog * Real.exp (-(inputLog + rFreq + 2)) ≤ Real.exp (-rFreq) / 2 := by
  have htwo : Real.log (2 : ℝ) ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  calc
    _ = Real.exp (-(rFreq + 2)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := precenter_exp_add_le_div rFreq 2 (by norm_num) htwo

end Erdos3.VectorPolynomial

end

end OAI
