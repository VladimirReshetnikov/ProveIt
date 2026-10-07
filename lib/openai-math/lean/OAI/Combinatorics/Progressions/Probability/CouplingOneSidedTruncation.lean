import OAI.Combinatorics.Progressions.Estimates.ScaledConditionedComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_ANOVA_right (S : Finset ι)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c w (productANOVA ν S f) =
      productCouplingPairing c (productANOVA μ S w) (productANOVA ν S f) := by
  have hw : w = fun x => ∑ T ∈ (Finset.univ : Finset ι).powerset, productANOVA μ T w x := by
    funext x
    rw [productANOVA_reconstruct, productConditionalMean_univ]
  calc
    _ = productCouplingPairing c
        (fun x => ∑ T ∈ (Finset.univ : Finset ι).powerset, productANOVA μ T w x)
        (productANOVA ν S f) := congrArg (fun u => productCouplingPairing c u (productANOVA ν S f)) hw
    _ = ∑ T ∈ (Finset.univ : Finset ι).powerset,
        productCouplingPairing c (productANOVA μ T w) (productANOVA ν S f) := by
      simp only [productCouplingPairing, Finset.sum_mul, FiniteProbabilityWeights.mean_sum]
    _ = _ := by
      apply Finset.sum_eq_single S
      · intro T _ hTS
        exact productCouplingPairing_ANOVA_ne c T S hTS w f
      · intro hS
        exact False.elim (hS (Finset.mem_powerset.mpr (Finset.subset_univ S)))

theorem productCouplingPairing_truncation_right (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c w (productANOVATruncation ν D f) =
      productTruncatedPairing c D w f := by
  rw [productTruncatedPairing, productCouplingPairing_truncation]
  change productCouplingPairing c w (fun y => ∑ S ∈ D, productANOVA ν S f y) = _
  simp only [productCouplingPairing, Finset.mul_sum, FiniteProbabilityWeights.mean_sum]
  apply Finset.sum_congr rfl
  intro S _
  exact productCouplingPairing_ANOVA_right c S w f

end Erdos3

end

end OAI
