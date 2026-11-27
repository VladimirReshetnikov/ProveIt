import GRHArticle.ProgressionFree.IntegerRationalDensityGap
import GRHArticle.ProgressionFree.IntegerFordDensity
import GRHArticle.ProgressionFree.IntegerSevenSmoothPacking

/-!
# McNew's Questions 7.1 and 7.3

These are comparisons between the suprema over actual sets of positive
integers. The rational-ratio case uses the finite prefix obstruction. The
integral-ratio case combines Ford's block construction and a fractional
packing of 7-smooth progressions.
-/

namespace GRHArticle.ProgressionFree

/-- The stronger integral-ratio gap obtained from the 268 packed triples
and the exact density of Ford's double block. -/
theorem integerIntegralDensitySupremum_gap_strong :
    (70515:ℝ)/1000000 < integerUpperDensitySupremum true - integerNaturalDensitySupremum true := by
  have hu := integerUpperDensitySupremum_integral_ford
  have hb := (integerNaturalDensitySupremum_le_smoothLower true 7).trans
    (integerSmoothLowerOptimization_seven_packing true)
  linarith only [hu,hb]

/-- Both quantitative assertions of the article's theorem on McNew's
Questions 7.1 and 7.3. -/
theorem mcNew_integer_density_gaps :
    (2836:ℝ)/1000000 < integerUpperDensitySupremum false - integerNaturalDensitySupremum false ∧
    (69218:ℝ)/1000000 < integerUpperDensitySupremum true - integerNaturalDensitySupremum true :=
  ⟨integerRationalDensitySupremum_gap, (by norm_num : (69218:ℝ)/1000000 < 70515/1000000).trans
    integerIntegralDensitySupremum_gap_strong⟩

end GRHArticle.ProgressionFree
