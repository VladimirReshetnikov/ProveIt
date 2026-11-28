import GRHArticle.ProgressionFree.PolynomialNaturalExchangeGain

/-!
# From a positive local exchange bracket to a strict natural-density gain
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- A positive bracket gives a strict gain, and the squarefree lower bound
gives an explicit lower estimate on the actual density difference. -/
theorem polynomialNaturalExchangeGain_bounds (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p)
    (hgain : 0 < naturalExchangeBracket (naturalExchangePrimeWeights S)) :
    0 < naturalExchangeGainLower (Fintype.card F : ℝ)⁻¹ (naturalExchangePrimeWeights S) ∧
      naturalExchangeGainLower (Fintype.card F : ℝ)⁻¹ (naturalExchangePrimeWeights S) ≤
        polynomialNaturalExchangeGain S := by
  let z := (Fintype.card F : ℝ)⁻¹
  let w (p : F[X]) := z^p.natDegree
  have hz := oneFreePrime_field_inv_bounds (F := F)
  have hw (p : F[X]) (hp : p ∈ S) : 0 < w p ∧ w p < 1 :=
    ⟨pow_pos hz.1 _, pow_lt_one₀ hz.1.le hz.2 (hS p hp).2.natDegree_pos.ne'⟩
  have hp : 0 < ∏ p ∈ S, w p := Finset.prod_pos (fun p hp ↦ (hw p hp).1)
  have hr : 0 < ∏ p ∈ S, (1-w p) := Finset.prod_pos (fun p hp ↦ sub_pos.mpr (hw p hp).2)
  have hb := greedyPrimeAvoidingDensity_ge_exclusion_product S hS
  change (1-z)*(∏ p ∈ S, (1-w p)) ≤ greedyPrimeAvoidingDensity S at hb
  have hfactor : naturalExchangeGainLower z (naturalExchangePrimeWeights S) =
      ((1-z)*(∏ p ∈ S, (1-w p))) * (∏ p ∈ S, w p) *
        naturalExchangeBracket (naturalExchangePrimeWeights S) := by
    simp only [naturalExchangeGainLower, naturalExchangePrimeWeights, List.map_map,
      Finset.prod_map_toList, Function.comp_def, w, z, Finset.prod_mul_distrib, mul_assoc]
  rw [hfactor]
  refine ⟨mul_pos (mul_pos (mul_pos (sub_pos.mpr hz.2) hr) hp) hgain, ?_⟩
  unfold polynomialNaturalExchangeGain
  rw [naturalExchangePrimeWeights, Finset.prod_map_toList]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hp.le) hgain.le

/-- A positive finite bracket yields an actual progression-free family with
strictly larger natural density than the greedy valuation family. -/
theorem polynomialNaturalExchange_strict_density (S : Finset F[X])
    (hS : ∀ p ∈ S, p.Monic ∧ Irreducible p)
    (hgain : 0 < naturalExchangeBracket (naturalExchangePrimeWeights S)) :
    PolynomialRatioThreeGPFree (polynomialNaturalExchangeFamily S) ∧
      ∃ g e : ℝ, Tendsto (polynomialBallProportion (polynomialValuationGreedySet F)) atTop (𝓝 g) ∧
        Tendsto (polynomialBallProportion (polynomialNaturalExchangeFamily S)) atTop (𝓝 e) ∧
        g < e ∧ e-g = polynomialNaturalExchangeGain S := by
  obtain ⟨g,hg,he⟩ := polynomialNaturalExchange_density_gain S hS
  have h := polynomialNaturalExchangeGain_bounds S hS hgain
  exact ⟨polynomialRatioThreeGPFree_naturalExchange S, g, g+polynomialNaturalExchangeGain S,
    hg, he, lt_add_of_pos_right _ (h.1.trans_le h.2), by ring⟩

end GRHArticle.ProgressionFree
