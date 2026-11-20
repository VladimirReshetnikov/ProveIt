import MoserWorm.Common.Interval.RationalBasic
import MoserWorm.Common.Interval.Sound

/-! Soundness of rational-constant enclosures. -/

namespace MoserWorm.DIval

theorem mem_ratio (num den : Int) (hden : 0 < den) :
    (num : ℝ) / (den : ℝ) ∈ ratio num den := by
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have floor_le (n : Int) : ((n.fdiv den : Int) : ℝ) * den ≤ n := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ hden.le]
    exact_mod_cast Int.ediv_mul_le n hden.ne'
  have hl := floor_le (num * dfxOne)
  have hr := floor_le (-num * dfxOne)
  have hs : (2 : ℝ) ^ dfxS = (dfxOne : ℝ) := by norm_num [dfxS, dfxOne]
  rw [mem_def]
  simp only [ratio, hs]
  push_cast at hl hr ⊢
  constructor
  · apply (le_div_iff₀ hd).mpr at hl
    simpa only [div_mul_eq_mul_div] using hl
  · apply (le_div_iff₀ hd).mpr at hr
    have hn := neg_le_neg hr
    simpa only [neg_div, neg_neg, neg_mul, div_mul_eq_mul_div] using hn

end MoserWorm.DIval
