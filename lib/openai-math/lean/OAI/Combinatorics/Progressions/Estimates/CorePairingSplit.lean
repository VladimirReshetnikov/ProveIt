import OAI.Combinatorics.Progressions.Probability.CylinderJointMass
import OAI.Combinatorics.Progressions.Probability.ProductDensityRepresentative

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_empty (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVA μ ∅ w) (productANOVA ν ∅ f) =
      (FiniteProbabilityWeights.pi μ).mean w * (FiniteProbabilityWeights.pi ν).mean f := by
  simp only [productCouplingPairing, productANOVA_empty, FiniteProbabilityWeights.mean_const]

theorem productCouplingPairing_core_split (J : Finset ι) {r b : ℕ} (hrb : r ≤ b)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVATruncation μ (restrictedDegreeSupports J b) w)
      (productANOVATruncation ν (restrictedDegreeSupports J b) f) =
      (FiniteProbabilityWeights.pi μ).mean w * (FiniteProbabilityWeights.pi ν).mean f +
        (∑ k ∈ Finset.range r, productCouplingPairing c
          (productANOVATruncation μ (J.powersetCard (k + 1)) w)
          (productANOVATruncation ν (J.powersetCard (k + 1)) f)) +
        productCouplingPairing c (productANOVATruncation μ (degreeTailSupports J r b) w)
          (productANOVATruncation ν (degreeTailSupports J r b) f) := by
  simp only [productCouplingPairing_truncation]
  rw [sum_restrictedDegreeSupports_split J hrb, sum_restrictedDegreeSupports_zero,
    productCouplingPairing_empty]

end Erdos3

end

end OAI
