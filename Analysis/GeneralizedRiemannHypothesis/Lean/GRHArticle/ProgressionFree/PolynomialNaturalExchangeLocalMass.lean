import GRHArticle.ProgressionFree.PolynomialPrimePowerDensity
import GRHArticle.ProgressionFree.PolynomialNaturalExchangeWeights

/-!
# Local masses of the deleted and added exponent vectors

The three product rules in the exchange use the strictly positive greedy
exponents, the cube on 1 and 2, and the all-ones vector.
-/

namespace GRHArticle.ProgressionFree

open scoped Classical BigOperators

/-- The positive part of the original ternary exponent rule. -/
def strictlyPositiveGreedyExponents : Set ℕ := {a | a ∈ greedyExponents ∧ a ≠ 0}

theorem primeExponentWeight_positiveGreedy {w : ℝ} (hw : 0 ≤ w) (hw' : w < 1) :
    primeExponentWeight w strictlyPositiveGreedyExponents = w * positiveGreedyWeight w := by
  let f := strictlyPositiveGreedyExponents.indicator (w^·)
  have hg := summable_geometric_of_lt_one hw hw'
  have hs : Summable f := hg.indicator _
  have hshift (n : ℕ) : f (n+1) = w * positiveGreedyWeightTerm w n := by
    by_cases h : n+1 ∈ greedyExponents <;>
      simp [f, strictlyPositiveGreedyExponents, positiveGreedyWeightTerm,
        h, pow_succ, mul_comm]
  change (∑' n, f n) = _
  rw [← hs.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, hshift, tsum_mul_left, positiveGreedyWeight]
  have hzero : f 0 = 0 := by simp [f, strictlyPositiveGreedyExponents]
  rw [hzero, zero_add]

theorem primeExponentWeight_cube (w : ℝ) :
    primeExponentWeight w ({1,2} : Set ℕ) = w*(1+w) := by
  unfold primeExponentWeight
  rw [tsum_eq_sum (s := ({1,2} : Finset ℕ))]
  · norm_num [Set.indicator]; ring
  · intro n hn
    simp_all [Set.indicator]

theorem primeExponentWeight_one (w : ℝ) : primeExponentWeight w ({1} : Set ℕ) = w := by
  unfold primeExponentWeight
  rw [tsum_eq_sum (s := ({1} : Finset ℕ))]
  · simp
  · intro n hn
    simp_all [Set.indicator]

end GRHArticle.ProgressionFree
