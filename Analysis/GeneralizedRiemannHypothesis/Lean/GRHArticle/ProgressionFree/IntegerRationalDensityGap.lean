import GRHArticle.ProgressionFree.IntegerPrimeGapCertificate
import GRHArticle.ProgressionFree.IntegerUpperDensityLowerBound
import GRHArticle.ProgressionFree.IntegerSmoothNaturalBound

/-!
# McNew's Question 7.1

The finite obstruction at 80 yields a strict gap between the two suprema
over admissible sets of positive integers with rational ratios.
-/

namespace GRHArticle.ProgressionFree

/-- The prime-tail version of the integer prefix obstruction at all cutoffs. -/
theorem integerDensitySupremum_gap_ge_primePrefix (integral : Bool) {N Y : ℕ} (hNY : N ≤ Y) :
    integerSmoothDensityFactor Y * (integerPrefixLoss integral N : ℝ) - integerPrimeSquareTail Y ≤
      integerUpperDensitySupremum integral - integerNaturalDensitySupremum integral := by
  have hB := integerNaturalDensitySupremum_le_smoothLower integral Y
  have hU := integerSmoothUpperOptimization_sub_integerPrimeSquareTail_le_integerUpperDensitySupremum integral Y
  have hp := integerSmoothOptimization_gap integral hNY
  linarith only [hB, hU, hp]

/-- McNew's Question 7.1: upper density beats natural density for rational
ratios by more than the article's 0.002836. -/
theorem integerRationalDensitySupremum_gap :
    (2836:ℝ)/1000000 < integerUpperDensitySupremum false - integerNaturalDensitySupremum false :=
  rationalPrimePrefix_margin.trans_le (integerDensitySupremum_gap_ge_primePrefix false (by decide))

end GRHArticle.ProgressionFree
