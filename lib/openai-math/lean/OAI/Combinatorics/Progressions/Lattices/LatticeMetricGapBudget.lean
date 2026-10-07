import OAI.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_bchLatticeSeparationRadius_inv_exp_bound (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H l : ℕ) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      1 / bchLatticeSeparationRadius s d H l ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hmetric⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  refine ⟨C + 5, by omega, ?_⟩
  intro d H l p hp hd hH hl
  have hunit : ((1 : ℝ≥0) : ℝ) ≤ Real.exp ((p + 2) ^ 0) := by
    simpa only [NNReal.coe_one, pow_zero] using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  have hA := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  have hAq := (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H 1).trans
    (hmetric d H 1 p hp hd hH hunit)
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hpq : p ≤ (p + C) ^ C := by
    apply (show p ≤ p + C by linarith).trans
    simpa only [pow_one] using
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + C) (by omega : 1 ≤ C)
  have hprod := inverse_radius_product_exp_bound hA (by positivity : 0 ≤ (p + C) ^ C)
    hAq (hl.trans (Real.exp_le_exp.mpr hpq))
  calc
    1 / bchLatticeSeparationRadius s d H l =
        ((l : ℝ) + 1) * (bchBoxCoordinateBound s d H 1 + 1) := by
      simp only [bchLatticeSeparationRadius, bchLogMetricConstant, NNReal.toReal]
      field_simp
      norm_num
    _ ≤ 4 * ((l : ℝ) + 1) * (bchBoxCoordinateBound s d H 1 + 1) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ l + 1 by positivity) (by linarith : 0 ≤ bchBoxCoordinateBound s d H 1 + 1)]
    _ ≤ Real.exp (2 * (p + C) ^ C + 16) := hprod
    _ ≤ _ := Real.exp_le_exp.mpr (enlarged_power_dominates_twice_add_sixteen hp C hC)

theorem quotient_radius_inverse_le_exp {δ K p : ℝ} (hδ : 0 < δ) (hK : 0 < K)
    (hp : 0 ≤ p) (hδp : 1 / δ ≤ Real.exp p) (hKp : K ≤ Real.exp p) :
    1 / (δ / (4 * K)) ≤ Real.exp (2 * p + 16) := by
  have hprod := inverse_radius_product_exp_bound (show 0 ≤ 1 / δ by positivity) hp hδp hKp
  calc
    1 / (δ / (4 * K)) = 4 * K * (1 / δ) := by field_simp
    _ ≤ 4 * (K + 1) * (1 / δ + 1) := by
      nlinarith [mul_nonneg hK.le (show 0 ≤ 1 / δ by positivity)]
    _ ≤ _ := hprod

theorem quotient_radius_inverse_power_budget (A B : ℕ) (hA : 2 ≤ A) (hB : 2 ≤ B)
    {δ K p : ℝ} (hδ : 0 < δ) (hK : 0 < K) (hp : 0 ≤ p)
    (hδp : 1 / δ ≤ Real.exp ((p + A) ^ A)) (hKp : K ≤ Real.exp ((p + B) ^ B)) :
    1 / (δ / (4 * K)) ≤ Real.exp ((p + (A + B + 5 : ℕ)) ^ (A + B + 5)) := by
  have hqδ := hδp.trans (Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := A) (D := A + B) hp (by omega) (by omega)))
  have hqK := hKp.trans (Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := B) (D := A + B) hp (by omega) (by omega)))
  exact (quotient_radius_inverse_le_exp hδ hK (by positivity) hqδ hqK).trans
    (Real.exp_le_exp.mpr (enlarged_power_dominates_twice_add_sixteen hp (A + B) (by omega)))

end Erdos3

end

end OAI
