import OAI.Combinatorics.Progressions.Estimates.MixedCoveredSiteExtraction

namespace OAI

section

namespace Erdos3

noncomputable def finiteRowChartRadius (rows dim : ℕ) (C T : ℝ) : ℝ :=
  1 / (4 * ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1))

theorem finiteRowChartRadius_pos (rows dim : ℕ) {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T) :
    0 < finiteRowChartRadius rows dim C T := by
  unfold finiteRowChartRadius
  positivity

theorem finiteRowChartRadius_budget (rows dim : ℕ) {C T R : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hsmall : R ≤ finiteRowChartRadius rows dim C T) :
    (rows : ℝ) * (C * (((dim : ℝ) + 1) * (T * R))) ≤ 1 / 4 := by
  have hd : 0 < 4 * ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1) := by positivity
  have hr := (le_div_iff₀ hd).mp hsmall
  have hb : (rows : ℝ) * C * ((dim : ℝ) + 1) * T ≤
      ((rows : ℝ) + 1) * (C + 1) * ((dim : ℝ) + 1) * (T + 1) := by gcongr <;> linarith
  have hm := mul_le_mul_of_nonneg_right hb hR
  nlinarith only [hr, hm]

end Erdos3

end

section

namespace Erdos3

theorem finiteRowChartRadius_inv_le_exp (rows dim : ℕ) {C T P : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hP : 0 ≤ P)
    (hr : (rows : ℝ) ≤ Real.exp P) (hd : (dim : ℝ) ≤ Real.exp P)
    (hCP : C ≤ Real.exp P) (hTP : T ≤ Real.exp P) :
    (finiteRowChartRadius rows dim C T)⁻¹ ≤ Real.exp (4 * P + 6) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hunit : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hadd {a : ℝ} (ha : a ≤ Real.exp P) : a + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ 2 * Real.exp P := by linarith
      _ ≤ Real.exp P * Real.exp 1 := by nlinarith [Real.exp_pos P]
      _ = _ := (Real.exp_add _ _).symm
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) htwo 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  simp only [finiteRowChartRadius, one_div, inv_inv]
  calc
    _ ≤ Real.exp 2 * Real.exp (P + 1) * Real.exp (P + 1) * Real.exp (P + 1) * Real.exp (P + 1) := by
      gcongr
      · exact hadd hr
      · exact hadd hCP
      · exact hadd hd
      · exact hadd hTP
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
