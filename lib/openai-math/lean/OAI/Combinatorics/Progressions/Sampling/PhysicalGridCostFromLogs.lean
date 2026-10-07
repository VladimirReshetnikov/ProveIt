import OAI.Combinatorics.Progressions.Estimates.PhysicalCellLogCost

namespace OAI

section

namespace Erdos3

theorem physicalGridBudget_pay {rho A inverseLog ratioLog budget : ℝ}
    (hrho : 0 < rho) (hA : 0 ≤ A)
    (hinv : rho⁻¹ ≤ Real.exp inverseLog) (hratio : A ≤ Real.exp ratioLog)
    (hbudget : inverseLog + ratioLog + 2 ≤ budget) :
    4 * A * Real.exp (-budget) ≤ rho := by
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hprod : 4 * A * rho⁻¹ ≤ Real.exp (inverseLog + ratioLog + 2) := by
    calc
      _ ≤ Real.exp 2 * Real.exp ratioLog * Real.exp inverseLog :=
        mul_le_mul (mul_le_mul h4 hratio hA (Real.exp_nonneg _)) hinv
          (inv_nonneg.mpr hrho.le) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have he : Real.exp (inverseLog + ratioLog + 2) * Real.exp (-budget) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hpaid := (mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg (-budget))).trans he
  have h := mul_le_mul_of_nonneg_right hpaid hrho.le
  calc
    4 * A * Real.exp (-budget) = (4 * A * rho⁻¹ * Real.exp (-budget)) * rho := by
      field_simp
    _ ≤ 1 * rho := h
    _ = rho := one_mul _

theorem normalized_physical_cell_width_log_budget {I : Type*}
    (N : I → ℕ) (H : I → ℝ) (rho A inverseLog ratioLog budget : ℝ)
    (hH : ∀ i, 0 ≤ H i) (hrho : 0 < rho) (hA : 0 ≤ A)
    (hlarge : ∀ i, 4 ≤ rho * H i) (hwhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    (hsize : ∀ i, (N i : ℝ) ≤ A * H i)
    (hinv : rho⁻¹ ≤ Real.exp inverseLog) (hratio : A ≤ Real.exp ratioLog)
    (hbudget : inverseLog + ratioLog + 2 ≤ budget)
    (i : I) (c : (normalizedBoxPartitions N H rho hlarge hwhole i).Label) :
    Real.exp (-budget) * (N i : ℝ) ≤
      ((normalizedBoxPartitions N H rho hlarge hwhole i).length c : ℝ) := by
  have hp := physicalGridBudget_pay hrho hA hinv hratio hbudget
  have hcost := mul_le_mul_of_nonneg_right hp (hH i)
  have hn := mul_le_mul_of_nonneg_left (hsize i) (Real.exp_nonneg (-budget))
  have hc := (normalizedBoxPartitions_lengths N H rho hlarge hwhole i c).1
  nlinarith

end Erdos3

end

end OAI
