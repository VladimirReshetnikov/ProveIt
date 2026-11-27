import GRHArticle.ProgressionFree.IntegerBoundaryExchange
import GRHArticle.ProgressionFree.IntegerBoundaryExchangeMargin
import GRHArticle.ProgressionFree.IntegerMcNewGaps

/-!
# McNew's Question 7.4 and the three density separations

Compare the actual natural-density suprema, using the local 5-smooth
exchange and the global estimates through cutoff 6619.
-/

namespace GRHArticle.ProgressionFree

/-- McNew's Question 7.4, with a slightly stronger numerical margin than
the one stated in article theorem `gpi:thm:beta-alpha`. -/
theorem integerNaturalDensitySupremum_integral_sub_rational :
    (135206 : ℝ)/10^9 < integerNaturalDensitySupremum true - integerNaturalDensitySupremum false :=
  integerBoundaryExchange_margin.trans_le (integerBoundaryGain_density_bridge
    integerExchangeGain (fun n hn ↦ (integerExchangeReplacement_smooth n hn).1)
    integerExchangeReplacement_admissible
    (fun _ ha hf ↦ integerExchange_boundary_gain ha hf) (Y := 6619) (by decide))

/-- The precise lower bound printed in the article. -/
theorem mcNew_integer_ratio_gap :
    (135102729954660 : ℝ)/10^18 ≤
      integerNaturalDensitySupremum true - integerNaturalDensitySupremum false :=
  (by norm_num : (135102729954660 : ℝ)/10^18 ≤ 135206/10^9).trans
    integerNaturalDensitySupremum_integral_sub_rational.le

end GRHArticle.ProgressionFree
