import GRHArticle.ProgressionFree.TriangleRothThirty
import GRHArticle.ProgressionFree.IntervalRothNumbers32

/-!
# Strictness of the one-prime polynomial density bound

The finite triangle certificates and exact Roth table close the
two-prime estimate in `gpp:thm:twoprime`, including its binary case.
-/

namespace GRHArticle.ProgressionFree

theorem twoPrimeTriangleBound_verified : TwoPrimeTriangleBound :=
  fun A hL hr hc ↦ card_triangle_le_roth_rows_sub_penalty A hL hr hc

/-- The three explicit losses for the actual polynomial-ratio supremum
over any finite field. -/
theorem polynomialRatioDensitySupremum_le_twoPrime (F : Type*) [Field F] [Fintype F] :
    polynomialRatioDensitySupremum F ≤
      let z := (Fintype.card F : ℝ)⁻¹
      polynomialOnePrimeRothBound F - (1-z)^2*(z^8+z^19+z^29) :=
  polynomialRatioDensitySupremum_le_twoPrime_of_triangle F twoPrimeTriangleBound_verified

/-- Asada et al.'s one-prime upper bound is strict over every finite
field, answering Question 6.2. -/
theorem polynomialRatioDensitySupremum_lt_onePrime (F : Type*) [Field F] [Fintype F] :
    polynomialRatioDensitySupremum F < polynomialOnePrimeRothBound F :=
  polynomialRatioDensitySupremum_lt_onePrime_of_triangle F twoPrimeTriangleBound_verified

/-- The exact binary rational bound and its strict decimal comparison. -/
theorem polynomialRatioDensitySupremum_binary_upper (F : Type*) [Field F] [Fintype F]
    (hq : Fintype.card F = 2) :
    polynomialRatioDensitySupremum F ≤ (907739729:ℝ)/1073741824 ∧
      (907739729:ℝ)/1073741824 < 0.845398501494 :=
  polynomialRatioDensitySupremum_binary_le_of_rothTable F hq twoPrimeTriangleBound_verified
    rothNumberNat_eq_binaryRothNumberTable

/-- Positive separation from the greedy benchmark is less than
`5.46 × 10⁻⁷` over the binary field. -/
theorem polynomialRatioDensitySupremum_binary_gap (F : Type*) [Field F] [Fintype F]
    (hq : Fintype.card F = 2) :
    0 < polynomialRatioDensitySupremum F - polynomialDegreeBenchmark F ∧
      polynomialRatioDensitySupremum F - polynomialDegreeBenchmark F < 5.46e-7 :=
  polynomialRatioDensitySupremum_binary_gap_of_rothTable F hq twoPrimeTriangleBound_verified
    rothNumberNat_eq_binaryRothNumberTable

end GRHArticle.ProgressionFree
