import GRHArticle.ProgressionFree.NumberFieldIdeals.LocalMassBounds
import GRHArticle.ProgressionFree.NumberFieldIdeals.PrimeNormTailBound

/-!
# Error from omitting exterior exponent rules

The loss of an infinite product of local probabilities is at most the sum
of the individual losses. Allowing exponents zero and one gives an explicit
degree-over-cutoff bound, uniformly in all the other allowed exponents.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter

variable {K : Type*} [Field K] [NumberField K]

private theorem one_sub_prod_le_sum_loss {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1-f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi]
    have hprod : ∏ j ∈ s, f j ≤ 1 := prod_le_one (fun j _ ↦ (hf j).1) (fun j _ ↦ (hf j).2)
    nlinarith only [ih, mul_nonneg (sub_nonneg.mpr (hf i).2) (sub_nonneg.mpr hprod)]

/-- The loss is bounded by the sum of the inverse squared norms over the
chosen primes, even for different infinite exponent sets at every prime. -/
theorem one_sub_localRuleProduct_le_tsum_sq {ι : Type*} (v : ι → HeightOneSpectrum (𝓞 K))
    (hv : Function.Injective v) (A : ι → Set ℕ) (h0 : ∀ i, 0 ∈ A i) (h1 : ∀ i, 1 ∈ A i) :
    1 - ∏' i, localRuleMass (v i) (A i) ≤ ∑' i, ((absNorm (v i).asIdeal : ℝ)^2)⁻¹ := by
  have hm := (localRuleEulerProductOn v hv ∅ A h0 (fun i _ ↦ h1 i)).1
  have hs := (summable_primeIdeal_inv_sq_absNorm (K := K)).comp_injective hv
  apply le_of_tendsto (tendsto_const_nhds.sub hm.hasProd)
  apply Eventually.of_forall
  intro s
  calc
    _ ≤ ∑ i ∈ s, (1-localRuleMass (v i) (A i)) :=
      one_sub_prod_le_sum_loss s _ (fun i ↦ localRuleMass_mem_unitInterval (v i) (A i))
    _ ≤ ∑ i ∈ s, ((absNorm (v i).asIdeal : ℝ)^2)⁻¹ := sum_le_sum fun i _ ↦ by
      simpa only [primeWeight, inv_pow] using one_sub_localRuleMass_le_sq (v i) (h0 i) (h1 i)
    _ ≤ _ := hs.sum_le_tsum s (fun i _ ↦ by change 0 ≤ ((absNorm (v i).asIdeal : ℝ)^2)⁻¹; positivity)

/-- Uniform quantitative Euler-product tail in the ideal density comparison. -/
theorem one_sub_exteriorRuleProduct_le_finrank_div (Y : ℕ) (hY : 0 < Y)
    (A : {p : HeightOneSpectrum (𝓞 K) // Y < absNorm p.asIdeal} → Set ℕ)
    (h0 : ∀ p, 0 ∈ A p) (h1 : ∀ p, 1 ∈ A p) :
    1 - ∏' p, localRuleMass p.val (A p) ≤ (Module.finrank ℚ K : ℝ) / Y :=
  (one_sub_localRuleProduct_le_tsum_sq Subtype.val Subtype.val_injective A h0 h1).trans
    (primeIdeal_inv_sq_tail_le_finrank_div Y hY)

end GRHArticle.ProgressionFree.NumberFieldIdeals
