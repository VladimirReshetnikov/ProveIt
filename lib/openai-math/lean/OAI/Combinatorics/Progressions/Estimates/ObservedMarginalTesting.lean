import OAI.Combinatorics.Progressions.Probability.ObservedDensityTesting

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i) (hμ : ∀ i x, 0 < (μ i).weight x)

include hμ

theorem observedProductDensity_test_error (S : Finset ι) (g : (∀ i, X i) → ℝ)
    {eta C : ℝ} (heta : 0 ≤ eta) (hg : ProductDependsOn S g)
    (hclose : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ S (observedProductDensity μ p F (fun _ => 1)) x - 1| ≤ eta)
    (hcap : ∀ x, |g x| ≤ C) :
    |p.mean (fun z => g (F z)) - (FiniteProbabilityWeights.pi μ).mean g| ≤ eta * C := by
  have h := productMarginal_test_error μ (observedProductDensity μ p F (fun _ => 1))
    g S heta hg hclose (fun x _ => hcap x)
  rw [observedProductDensity_test μ p F hμ] at h
  simpa only [one_mul] using h

theorem observedProductDensity_family_test_error (D : Finset (Finset ι))
    (g : Finset ι → (∀ i, X i) → ℝ) {b : ℕ} {eta C : ℝ} (heta : 0 ≤ eta)
    (hcard : ∀ S ∈ D, S.card ≤ b) (hg : ∀ S ∈ D, ProductDependsOn S (g S))
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) eta b)
    (hcap : ∀ S ∈ D, ∀ x, |g S x| ≤ C) :
    |p.mean (fun z => ∑ S ∈ D, g S (F z)) -
      (FiniteProbabilityWeights.pi μ).mean (fun x => ∑ S ∈ D, g S x)| ≤
      eta * D.card * C := by
  simp only [FiniteProbabilityWeights.mean_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ S ∈ D, |p.mean (fun z => g S (F z)) - (FiniteProbabilityWeights.pi μ).mean (g S)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ D, eta * C := by
      apply Finset.sum_le_sum
      intro S hS
      exact observedProductDensity_test_error μ p F hμ S (g S) heta (hg S hS)
        (hclose S (hcard S hS)) (hcap S hS)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
