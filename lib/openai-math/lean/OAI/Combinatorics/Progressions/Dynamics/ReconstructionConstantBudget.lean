import Mathlib

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem ambientReconstructionConstant_le_exp (L K B T ε : ℝ≥0) (r : ℝ) (hr : 1 ≤ r)
    (hL : (L : ℝ) ≤ Real.exp r) (hK : (K : ℝ) ≤ Real.exp r)
    (hB : (B : ℝ) ≤ Real.exp r) (hT : (T : ℝ) ≤ Real.exp r)
    (hε : (ε : ℝ)⁻¹ ≤ Real.exp r) :
    ((2 * max (L * (2 * K)) (2 * B / (min T⁻¹ ε / 2)) : ℝ≥0) : ℝ) ≤ Real.exp (5 * r) := by
  have h2 : (2 : ℝ) ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  let m := min T⁻¹ ε
  have hm : (m : ℝ)⁻¹ ≤ Real.exp r := by
    by_cases h : T⁻¹ ≤ ε
    · simp only [m, min_eq_left h, NNReal.coe_inv, inv_inv]
      exact hT
    · simp only [m, min_eq_right (le_of_not_ge h)]
      exact hε
  have hfirst : (L : ℝ) * (2 * K) ≤ Real.exp (4 * r) := by
    calc
      _ ≤ Real.exp r * (Real.exp r * Real.exp r) := by gcongr
      _ = Real.exp (3 * r) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hsecond : 2 * (B : ℝ) / ((m : ℝ) / 2) ≤ Real.exp (4 * r) := by
    calc
      _ = 2 * 2 * (B : ℝ) * (m : ℝ)⁻¹ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
      _ ≤ Real.exp r * Real.exp r * Real.exp r * Real.exp r := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  change 2 * max ((L : ℝ) * (2 * K)) (2 * (B : ℝ) / ((m : ℝ) / 2)) ≤ _
  calc
    _ ≤ Real.exp r * Real.exp (4 * r) := mul_le_mul h2 (max_le hfirst hsecond) (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem generalReconstructionConstant_le_exp (L B A N T D Q X Y ε : ℝ≥0) (r : ℝ) (hr : 1 ≤ r)
    (hL : (L : ℝ) ≤ Real.exp r) (hB : (B : ℝ) ≤ Real.exp r)
    (hA : (A : ℝ) ≤ Real.exp r) (hN : (N : ℝ) ≤ Real.exp r)
    (hT : (T : ℝ) ≤ Real.exp r) (hD : (D : ℝ) ≤ Real.exp r)
    (hQ : (Q : ℝ) ≤ Real.exp r) (hX : (X : ℝ) ≤ Real.exp r)
    (hY : (Y : ℝ) ≤ Real.exp r)
    (hε : (ε : ℝ)⁻¹ = (T : ℝ) * Y + D * Q * X * T * Y + 1) :
    ((2 * max (L * (2 * (A * N * T))) (2 * B / (min T⁻¹ ε / 2)) : ℝ≥0) : ℝ) ≤
      Real.exp (40 * r) := by
  have h15 : 1 ≤ Real.exp (5 * r) := Real.one_le_exp (by linarith)
  have hTY : (T : ℝ) * Y ≤ Real.exp (5 * r) := by
    calc
      _ ≤ Real.exp r * Real.exp r := by gcongr
      _ = Real.exp (2 * r) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hprod : (D : ℝ) * Q * X * T * Y ≤ Real.exp (5 * r) := by
    calc
      _ ≤ Real.exp r * Real.exp r * Real.exp r * Real.exp r * Real.exp r := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have heps : (ε : ℝ)⁻¹ ≤ Real.exp (8 * r) := by
    rw [hε]
    calc
      _ ≤ 3 * Real.exp (5 * r) := by linarith
      _ ≤ Real.exp (3 * r) * Real.exp (5 * r) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp (3 * r)]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hK : ((A * N * T : ℝ≥0) : ℝ) ≤ Real.exp (8 * r) := by
    calc
      _ ≤ Real.exp r * Real.exp r * Real.exp r := by simp only [NNReal.coe_mul]; gcongr
      _ = Real.exp (3 * r) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hshift : Real.exp r ≤ Real.exp (8 * r) := Real.exp_le_exp.mpr (by linarith)
  have h := ambientReconstructionConstant_le_exp L (A * N * T) B T ε (8 * r)
    (by linarith) (hL.trans hshift) hK (hB.trans hshift) (hT.trans hshift) heps
  convert h using 1
  congr 1
  ring

end Erdos3

end

end OAI
