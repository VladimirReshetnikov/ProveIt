import GRHArticle.ProgressionFree.PolynomialNaturalExchangeRule
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Positive greedy exponent weights in the polynomial exchange

The old strictly positive exponents contribute the shifted series
`T(w)`. A finite prefix and a geometric tail give certified comparisons
for the small fields in the natural-density exchange.
-/

namespace GRHArticle.ProgressionFree

open scoped Classical BigOperators

/-- The weight of an allowed exponent after removing one copy of the prime. -/
noncomputable def positiveGreedyWeightTerm (w : ℝ) (n : ℕ) : ℝ :=
  if n+1 ∈ greedyExponents then w^n else 0

/-- Local series in the deleted positive orthant of the greedy rule. -/
noncomputable def positiveGreedyWeight (w : ℝ) : ℝ := ∑' n, positiveGreedyWeightTerm w n

theorem positiveGreedyWeightTerm_bounds {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    0 ≤ positiveGreedyWeightTerm w n ∧ positiveGreedyWeightTerm w n ≤ w^n := by
  unfold positiveGreedyWeightTerm
  split <;> simp [pow_nonneg hw]

theorem positiveGreedyWeight_nonneg {w : ℝ} (hw : 0 ≤ w) : 0 ≤ positiveGreedyWeight w :=
  tsum_nonneg fun n ↦ (positiveGreedyWeightTerm_bounds hw n).1

/-- A cutoff bound at every depth. Only terms from the greedy prefix
enter the finite sum. -/
theorem positiveGreedyWeight_le_prefix {w : ℝ} (hw : 0 ≤ w) (hw' : w < 1) (L : ℕ) :
    positiveGreedyWeight w ≤
      (∑ n ∈ Finset.range L, positiveGreedyWeightTerm w n) + w^L/(1-w) := by
  have hg := summable_geometric_of_lt_one hw hw'
  have hs := Summable.of_nonneg_of_le (fun n ↦ (positiveGreedyWeightTerm_bounds hw n).1)
    (fun n ↦ (positiveGreedyWeightTerm_bounds hw n).2) hg
  unfold positiveGreedyWeight
  rw [← hs.sum_add_tsum_nat_add L]
  gcongr
  calc
    _ ≤ ∑' n : ℕ, w^(n+L) := ((summable_nat_add_iff L).mpr hs).tsum_le_tsum
      (fun n ↦ (positiveGreedyWeightTerm_bounds hw (n+L)).2) ((summable_nat_add_iff L).mpr hg)
    _ = _ := by simp_rw [pow_add]; rw [tsum_mul_right, tsum_geometric_of_lt_one hw hw']; ring

theorem positiveGreedyWeight_le_quadratic {w : ℝ} (hw : 0 ≤ w) (hw' : w < 1) :
    positiveGreedyWeight w ≤ 1 + w^2/(1-w) := by
  simpa [Finset.sum_range_succ, positiveGreedyWeightTerm, one_mem_greedyExponents,
    two_notMem_greedyExponents] using positiveGreedyWeight_le_prefix hw hw' 2

/-- The first eight exponents give a sharper bound for small finite fields. -/
theorem positiveGreedyWeight_le_eight {w : ℝ} (hw : 0 ≤ w) (hw' : w < 1) :
    positiveGreedyWeight w ≤ 1 + w^2 + w^3 + w^8/(1-w) := by
  have hp : ∀ n : Fin 8, n.val+1 ∈ greedyExponents ↔ n.val = 0 ∨ n.val = 2 ∨ n.val = 3 := by
    change ∀ n : Fin 8, (∀ d ∈ Nat.digits 3 (n.val+1), d ≤ 1) ↔ _
    decide
  have ht (n : ℕ) (hn : n < 8) : positiveGreedyWeightTerm w n =
      if n = 0 ∨ n = 2 ∨ n = 3 then w^n else 0 := by
    simp only [positiveGreedyWeightTerm, hp ⟨n, hn⟩]
  have hpre : (∑ n ∈ Finset.range 8, positiveGreedyWeightTerm w n) = 1+w^2+w^3 := by
    simp [Finset.sum_range_succ, ht _ (by decide : 7 < 8), ht _ (by decide : 6 < 8),
      ht _ (by decide : 5 < 8), ht _ (by decide : 4 < 8), ht _ (by decide : 3 < 8),
      ht _ (by decide : 2 < 8), ht _ (by decide : 1 < 8), ht _ (by decide : 0 < 8)]
  simpa only [hpre] using positiveGreedyWeight_le_prefix hw hw' 8

end GRHArticle.ProgressionFree
