import GRHArticle.ProgressionFree.PolynomialBoundedReplacement
import GRHArticle.ProgressionFree.PolynomialMomentBudgetBounds
import GRHArticle.ProgressionFree.PolynomialRoughDensityBound

/-!
# The explicit search cutoff and upper-density margin

The integer mean and variance budgets locate an actual positive replacement
coefficient. The density of its glued replacement gives the universal
margin, with a sharper explicit statement at field size two.
-/

namespace GRHArticle.ProgressionFree

open Filter

/-- The cutoff from the integer moment budgets contains an actual replacement
coefficient at least one. -/
theorem polynomialReplacementCoefficient_positive_through_searchCutoff
    (F : Type*) [Field F] [Fintype F] :
    ∃ R ≤ polynomialSearchCutoff F, 1 ≤ polynomialReplacementCoefficient F R := by
  let B := polynomialMomentBudgets (fun d ↦ d * polynomialIrreducibleCount F d) 480
  obtain ⟨hmean, hvar⟩ := polynomialSmoothPrimes_momentBudgets F 480
  have hpos : 0 < B.2 := polynomialMomentBudgets_variance_pos F 480 (by decide)
  exact polynomialReplacementCoefficient_positive_of_moment_bounds F B.1 B.2 hpos hmean hvar

/-- The search cutoff gives the article's explicit positive margin over the
greedy degree-deficit rule for every finite field. -/
theorem polynomialRatioDensitySupremum_searchCutoff_lower
    (F : Type*) [Field F] [Fintype F] :
    let q : ℝ := Fintype.card F
    let margin := (q - 1) * polynomialRoughDensity F 480 * (1 / q ^ (polynomialSearchCutoff F + 1))
    polynomialDegreeBenchmark F + margin ≤ polynomialRatioDensitySupremum F ∧
      polynomialDegreeBenchmark F < polynomialDegreeBenchmark F + margin := by
  let q : ℝ := Fintype.card F
  have hq : 1 < q := by dsimp only [q]; exact_mod_cast Fintype.one_lt_card
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hc := polynomialRoughDensity_pos F 480
  obtain ⟨R, hR, hcoefficient⟩ := polynomialReplacementCoefficient_positive_through_searchCutoff F
  have hR' : R + 1 ≤ polynomialSearchCutoff F + 1 := Nat.succ_le_succ hR
  have hcoeff : (1 : ℝ) ≤ (polynomialReplacementCoefficient F R : ℝ) := by exact_mod_cast hcoefficient
  have hscaled : 1 / q ^ (polynomialSearchCutoff F + 1) ≤
      (polynomialReplacementCoefficient F R : ℝ) / q ^ (R + 1) :=
    (one_div_le_one_div_of_le (pow_pos hq₀ _) (pow_le_pow_right₀ hq.le hR')).trans
      (div_le_div_of_nonneg_right hcoeff (pow_nonneg hq₀.le _))
  have hfactor : 0 < (q - 1) * polynomialRoughDensity F 480 := mul_pos (sub_pos.mpr hq) hc
  have hfree : PolynomialRatioThreeGPFree (polynomialReplacementUnion (F := F) R) :=
    fun _ _ _ hr ↦ polynomialReplacementUnion_no_ratio_progression R hr
  refine ⟨?_, lt_add_of_pos_right _ (mul_pos hfactor (one_div_pos.mpr (pow_pos hq₀ _)))⟩
  exact (add_le_add_right (mul_le_mul_of_nonneg_left hscaled hfactor.le) _).trans
    ((polynomialReplacementUnion_density_lower F R).trans (le_polynomialRatioDensitySupremum hfree))

/-- At field size two, the explicit search margin is strictly larger than both
binary lower bounds from the article. -/
theorem binary_polynomialRatioDensitySupremum_searchCutoff
    (F : Type*) [Field F] [Fintype F] (hF : Fintype.card F = 2) :
    polynomialDegreeBenchmark F + (1 : ℝ) / 2 ^ (polynomialSearchCutoff F + 13) <
      polynomialRatioDensitySupremum F ∧
    polynomialDegreeBenchmark F + (1 : ℝ) / 2 ^ (2 ^ 476 : ℕ) <
      polynomialDegreeBenchmark F + (1 : ℝ) / 2 ^ (polynomialSearchCutoff F + 13) := by
  have hbase := (polynomialRatioDensitySupremum_searchCutoff_lower F).1
  simp only [hF, Nat.cast_ofNat, show (2:ℝ) - 1 = 1 by norm_num, one_mul] at hbase
  have hc := binary_polynomialRoughDensity_gt hF
  have hp : 0 < (1 : ℝ) / 2 ^ (polynomialSearchCutoff F + 1) := by positivity
  have heq : (1 : ℝ) / 2 ^ (polynomialSearchCutoff F + 13) =
      (1 / (2 : ℝ) ^ 12) * (1 / 2 ^ (polynomialSearchCutoff F + 1)) := by
    rw [show polynomialSearchCutoff F + 13 = 12 + (polynomialSearchCutoff F + 1) by omega,
      pow_add, one_div_mul_one_div]
  have hcut := (polynomialSearchCutoff_table F).1 hF
  constructor
  · apply lt_of_lt_of_le _ hbase
    rw [heq]
    exact add_lt_add_right (mul_lt_mul_of_pos_right hc hp) _
  · have hpower : (2 : ℝ) ^ (polynomialSearchCutoff F + 13) < (2 : ℝ) ^ (2 ^ 476 : ℕ) :=
      pow_lt_pow_right₀ (by norm_num) hcut
    exact add_lt_add_right (one_div_lt_one_div_of_lt (by positivity) hpower) _

end GRHArticle.ProgressionFree
