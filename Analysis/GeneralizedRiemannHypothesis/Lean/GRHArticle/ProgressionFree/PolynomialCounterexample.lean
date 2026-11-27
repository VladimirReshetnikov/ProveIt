import GRHArticle.ProgressionFree.PolynomialRoughDensity
import GRHArticle.ProgressionFree.PolynomialDensitySupremum
import GRHArticle.ProgressionFree.PolynomialReplacementUnion

/-!
# The counterexample to the polynomial-ratio density conjecture

The signed gain counts actual smooth polynomials. The density multiplier
is the limit for actual squarefree rough polynomials over the same finite field.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped BigOperators Classical

/-- The limiting density `m_q` of the original greedy degree-deficit rule. -/
noncomputable def polynomialDegreeBenchmark (F : Type*) [Field F] [Fintype F] : ℝ :=
  (1 - (Fintype.card F : ℝ)⁻¹) *
    ∑' d : ℕ, greedyExponents.indicator (fun d ↦ (Fintype.card F : ℝ)⁻¹ ^ d) d

/-- The signed change per marked monic rough class, with scalars counted separately. -/
noncomputable def polynomialReplacementCoefficient (F : Type*) [Field F] [Fintype F] (R : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (R + 1),
    ((polynomialSmoothLayer F 480 k).card : ℤ) * polynomialDeficitDifference (R-k)

variable (F : Type*) [Field F] [Fintype F]

/-- Exact asymptotic density of the modified finite balls at a fixed cutoff. -/
theorem tendsto_polynomialDeficitReplacement_proportion (R : ℕ) :
    Tendsto (fun N ↦ polynomialBallProportion (polynomialDeficitReplacement (F := F) N R) N)
      atTop (𝓝 (polynomialDegreeBenchmark F +
        ((Fintype.card F : ℝ) - 1) * polynomialRoughDensity F 480 *
        ((polynomialReplacementCoefficient F R : ℝ) / (Fintype.card F : ℝ)^(R+1)))) := by
  have hbase := tendsto_polynomialBallProportion_deficit (F := F) greedyExponents
  have hrough := (tendsto_polynomialSquarefreeRoughLayer_card_div_pow F 480).comp
    (tendsto_sub_atTop_nat R)
  apply (hbase.add ((hrough.const_mul ((Fintype.card F : ℝ) - 1)).mul_const
    ((polynomialReplacementCoefficient F R : ℝ) / (Fintype.card F : ℝ)^(R+1)))).congr'
  filter_upwards [eventually_ge_atTop R] with N hNR
  exact (eq_add_of_sub_eq' (polynomialBallProportion_replacement_sub (F := F) hNR)).symm

/-- Quantitative lower bound for the upper density of the single infinite glued set. -/
theorem polynomialReplacementUnion_density_lower (R : ℕ) :
    polynomialDegreeBenchmark F + ((Fintype.card F : ℝ) - 1) * polynomialRoughDensity F 480 *
        ((polynomialReplacementCoefficient F R : ℝ) / (Fintype.card F : ℝ)^(R+1)) ≤
      limsup (polynomialBallProportion (polynomialReplacementUnion (F := F) R)) atTop :=
  polynomialReplacementUnion_le_limsup R (tendsto_polynomialDeficitReplacement_proportion F R)

/-- The article's counterexample to Conjecture 6.3 of Asada–Fourakis–Manski–McNew–Miller–Moreland,
for every finite field. The set is infinite and uses precisely the polynomial-ratio convention. -/
theorem exists_infinite_polynomialRatioThreeGPFree_strictUpperDensity :
    ∃ E : Set (Polynomial F), E.Infinite ∧ PolynomialRatioThreeGPFree E ∧
      polynomialDegreeBenchmark F < limsup (polynomialBallProportion E) atTop := by
  obtain ⟨R, hR⟩ := polynomialSmoothLayer_exists_positive_gain (F := F) 480
  have hq : 1 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hpos : 0 < (polynomialReplacementCoefficient F R : ℝ) := by
    exact_mod_cast (show 0 < polynomialReplacementCoefficient F R from lt_of_lt_of_le (by decide) hR)
  have hgain : 0 < ((Fintype.card F : ℝ) - 1) * polynomialRoughDensity F 480 *
      ((polynomialReplacementCoefficient F R : ℝ) / (Fintype.card F : ℝ)^(R+1)) :=
    mul_pos (mul_pos (sub_pos.mpr hq) (polynomialRoughDensity_pos F 480))
      (div_pos hpos (pow_pos (by linarith) _))
  exact ⟨polynomialReplacementUnion R, polynomialReplacementUnion_infinite R,
    fun _ _ _ hr ↦ polynomialReplacementUnion_no_ratio_progression R hr,
    (lt_add_of_pos_right _ hgain).trans_le (polynomialReplacementUnion_density_lower F R)⟩

/-- The supremum over polynomial-ratio progression-free sets is strictly greater than `m_q`. -/
theorem polynomialDegreeBenchmark_lt_polynomialRatioDensitySupremum :
    polynomialDegreeBenchmark F < polynomialRatioDensitySupremum F := by
  obtain ⟨E, _, hfree, hgain⟩ := exists_infinite_polynomialRatioThreeGPFree_strictUpperDensity F
  exact hgain.trans_le (le_polynomialRatioDensitySupremum hfree)

end GRHArticle.ProgressionFree
