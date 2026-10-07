import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem exp_neg_le_exp_neg_div_eight {A B : ℝ} (hAB : B + 4 ≤ A) :
    Real.exp (-A) ≤ Real.exp (-B) / 8 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 4 := by
    calc
      8 ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp (-(B + 4)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 4 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h8

theorem exp_neg_le_half_exp_neg {A B : ℝ} (hAB : B + 1 ≤ A) :
    Real.exp (-A) ≤ (1 / 2) * Real.exp (-B) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp (-(B + 1)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 1 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (-B) / 2 := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h2
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

theorem slicedSourceAccuracy_bounds {Q G E : ℝ} (hQ : 0 ≤ Q) (hG : 0 ≤ G) (hE : 0 ≤ E) :
    let εgrid := Real.exp (-(Q + E + 1))
    let εlong := Real.exp (-(G + E + 1))
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Q + E + 1) ∧
    0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ = Real.exp (G + E + 1) ∧
    ∀ C : ℝ, C ≤ Real.exp G → Real.exp Q * εgrid + εlong * C ≤ Real.exp (-E) := by
  intro εgrid εlong
  have hg : εgrid ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hQ, hE])
  have hl : εlong ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hG, hE])
  refine ⟨Real.exp_pos _, hg, ?_, Real.exp_pos _, hl, ?_, ?_⟩
  · simp only [εgrid, Real.exp_neg, inv_inv]
  · simp only [εlong, Real.exp_neg, inv_inv]
  · intro C hC
    have hhalf := exp_neg_le_half_exp_neg (A := E + 1) (B := E) le_rfl
    have hgrid : Real.exp Q * εgrid = Real.exp (-(E + 1)) := by
      dsimp [εgrid]
      rw [← Real.exp_add]
      congr 1
      ring
    have hlong : εlong * Real.exp G = Real.exp (-(E + 1)) := by
      dsimp [εlong]
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ Real.exp Q * εgrid + εlong * Real.exp G :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hC (Real.exp_nonneg _))
      _ = 2 * Real.exp (-(E + 1)) := by rw [hgrid, hlong]; ring
      _ ≤ Real.exp (-E) := by linarith only [hhalf]

end Erdos3

end

end OAI
