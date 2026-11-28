import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# Explicit high-digit bounds for the four-prime boxes

The low ternary depths are two, two, one, and one. The rational coefficient
for the high-digit charge leaves a uniform margin at the three base tuples.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- The low ternary digit depths in the four-prime calculation. -/
def fourPrimeLowDigitDepth : Fin 4 → ℕ := ![2,2,1,1]

/-- The inclusive coordinate limits of the low exponent box. -/
def fourPrimeLowBoxLimit (i : Fin 4) : ℕ := 3 ^ fourPrimeLowDigitDepth i - 1

/-- The article's geometric upper bound on the two high-digit charges. -/
def fourPrimeHighDigitTail (q : Fin 4 → ℚ) : ℚ :=
  ∑ e : Fin 2,
    (∏ i : Fin 4, ∏ j ∈ range (fourPrimeLowDigitDepth i),
      (1 + 1 / q i ^ ((e.val+1) * 3^j))) *
    ((∏ i : Fin 4, (1 - 1 / q i ^ ((e.val+1) * 3^(fourPrimeLowDigitDepth i)))⁻¹) - 1)

/-- Exact residual margin for the base tuple beginning with 2 and 3. -/
theorem one_div_200_lt_fourPrimeMargin_2357 :
    (1:ℚ)/200 < 1 - 1/(21/20) - fourPrimeHighDigitTail ![2,3,5,7] := by
  norm_num [fourPrimeHighDigitTail,fourPrimeLowDigitDepth,Fin.sum_univ_succ,Fin.prod_univ_succ,
    Finset.prod_range_succ]

/-- Exact residual margin for the base tuple beginning with 2 and 5. -/
theorem one_div_200_lt_fourPrimeMargin_25711 :
    (1:ℚ)/200 < 1 - 1/(21/20) - fourPrimeHighDigitTail ![2,5,7,11] := by
  norm_num [fourPrimeHighDigitTail,fourPrimeLowDigitDepth,Fin.sum_univ_succ,Fin.prod_univ_succ,
    Finset.prod_range_succ]

/-- Exact residual margin for the base tuple beginning with 3 and 5. -/
theorem one_div_200_lt_fourPrimeMargin_35711 :
    (1:ℚ)/200 < 1 - 1/(21/20) - fourPrimeHighDigitTail ![3,5,7,11] := by
  norm_num [fourPrimeHighDigitTail,fourPrimeLowDigitDepth,Fin.sum_univ_succ,Fin.prod_univ_succ,
    Finset.prod_range_succ]

end GRHArticle.ProgressionFree
