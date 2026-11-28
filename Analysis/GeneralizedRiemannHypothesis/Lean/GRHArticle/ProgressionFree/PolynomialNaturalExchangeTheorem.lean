import GRHArticle.ProgressionFree.PolynomialNaturalExchangeComparison
import GRHArticle.ProgressionFree.PolynomialNaturalExchangePrimes

/-!
# An explicit polynomial exchange beating the greedy natural density

The selected primes consist of all linears for field sizes at least four,
with the printed quadratic and cubic choices in the two smaller fields.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped Classical BigOperators

variable (F : Type*) [Field F] [Fintype F]

/-- Asada et al.'s Question 6.1. The specified family uses exactly
`max(q,4)` primes, avoids all positive-degree polynomial-ratio triples, and
has strictly larger natural density than the actual greedy set. -/
theorem polynomialNaturalExchange_beats_greedy :
    let S := naturalExchangeSelectedPrimes F
    S.card = max (Fintype.card F) 4 ∧ PolynomialRatioThreeGPFree (polynomialNaturalExchangeFamily S) ∧
      ∃ g e : ℝ, Tendsto (polynomialBallProportion (polynomialValuationGreedySet F)) atTop (𝓝 g) ∧
        Tendsto (polynomialBallProportion (polynomialNaturalExchangeFamily S)) atTop (𝓝 e) ∧
        g < e ∧ e-g = polynomialNaturalExchangeGain S :=
  ⟨card_naturalExchangeSelectedPrimes, polynomialNaturalExchange_strict_density _
    (fun _ hp ↦ mem_naturalExchangeSelectedPrimes hp) naturalExchangeBracket_selected_pos⟩

/-- Strict lower bounds on the actual density improvement in the three
small-field examples, in the order 2, 3, 4. -/
theorem polynomialNaturalExchange_gain_small :
    let d := polynomialNaturalExchangeGain (naturalExchangeSelectedPrimes F)
    (Fintype.card F = 2 → (4244:ℝ)/100000000 < d) ∧
    (Fintype.card F = 3 → (7119:ℝ)/100000000 < d) ∧
    (Fintype.card F = 4 → (8364:ℝ)/100000000 < d) := by
  have hb := (polynomialNaturalExchangeGain_bounds (naturalExchangeSelectedPrimes F)
    (fun _ hp ↦ mem_naturalExchangeSelectedPrimes hp) naturalExchangeBracket_selected_pos).2
  have h := naturalExchangeGainLower_selected_small (F := F)
  exact ⟨fun hq ↦ (h.1 hq).trans_le hb, fun hq ↦ (h.2.1 hq).trans_le hb,
    fun hq ↦ (h.2.2 hq).trans_le hb⟩

/-- A uniform explicit gain for every larger field from the quadratic
binomial estimate for the all-linear exchange. -/
theorem polynomialNaturalExchange_gain_large (hq : 5 ≤ Fintype.card F) :
    let z := (Fintype.card F : ℝ)⁻¹
    (1-z)^(Fintype.card F + 1) * z^(Fintype.card F) / 15 ≤
      polynomialNaturalExchangeGain (naturalExchangeSelectedPrimes F) := by
  let q := Fintype.card F
  let z := (q:ℝ)⁻¹
  have hz : 0 < z ∧ z < 1 := oneFreePrime_field_inv_bounds (F := F)
  have hb := (polynomialNaturalExchangeGain_bounds (naturalExchangeSelectedPrimes F)
    (fun _ hp ↦ mem_naturalExchangeSelectedPrimes hp) naturalExchangeBracket_selected_pos).2
  change naturalExchangeGainLower z (naturalExchangeSelectedWeights F) ≤ _ at hb
  rw [naturalExchangeSelectedWeights_linear (by omega : 4 ≤ Fintype.card F)] at hb
  have hl := naturalExchangeBracket_linear_lower q hq
  have heq : 1/(q:ℝ) = z := one_div _
  change naturalExchangeGainLower z (List.replicate q (1/(q:ℝ))) ≤ _ at hb
  rw [heq] at hb hl
  simp only [naturalExchangeGainLower, List.map_replicate, List.prod_replicate] at hb
  have h₀ : 0 ≤ 1-z := sub_nonneg.mpr hz.2.le
  have hfac : 0 ≤ (1-z)*((1-z)*z)^q := mul_nonneg h₀ (pow_nonneg (mul_nonneg h₀ hz.1.le) _)
  calc
    (1-z)^(q+1)*z^q/15 = (1-z)*((1-z)*z)^q * (1/15) := by rw [mul_pow, pow_succ]; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hl hfac).trans hb

end GRHArticle.ProgressionFree
