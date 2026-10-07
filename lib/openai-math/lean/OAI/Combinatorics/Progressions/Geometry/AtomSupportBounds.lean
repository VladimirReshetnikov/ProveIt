import OAI.Combinatorics.Progressions.Probability.CylinderJointMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productFiberIndicator_sq_mean_le_one (μ : ∀ i, FiniteProbabilityWeights (X i))
    (I : Finset ι) (x : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean (fun z => productFiberIndicator I x z ^ 2) ≤ 1 := by
  apply (FiniteProbabilityWeights.mean_mono _ (g := fun _ => (1 : ℝ)) _).trans_eq
    (FiniteProbabilityWeights.mean_const _ 1)
  intro z
  unfold productFiberIndicator
  split_ifs <;> norm_num

theorem productCouplingPairing_atom_component_le_one
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
    (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i)) (I A : Finset ι)
    (x : ∀ i, X i) (y : ∀ i, Y i) :
    |productCouplingPairing c (productANOVA μ A (productFiberIndicator I x))
      (productANOVA ν A (productFiberIndicator I y))| ≤ 1 := by
  have hx := (productANOVAEnergy_le_mean_sq μ {A} (productFiberIndicator I x)).trans
    (productFiberIndicator_sq_mean_le_one μ I x)
  have hy := (productANOVAEnergy_le_mean_sq ν {A} (productFiberIndicator I y)).trans
    (productFiberIndicator_sq_mean_le_one ν I y)
  simp only [productANOVAEnergy, Finset.sum_singleton] at hx hy
  have hc := productCouplingPairing_sq_le c (productANOVA μ A (productFiberIndicator I x))
    (productANOVA ν A (productFiberIndicator I y))
  have hb := hc.trans ((mul_le_of_le_one_left
    (FiniteProbabilityWeights.mean_nonneg _ (fun z => sq_nonneg (productANOVA ν A (productFiberIndicator I y) z))) hx).trans hy)
  apply (sq_le_sq₀ (abs_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)).mp
  simpa only [sq_abs, one_pow] using hb

end Erdos3

end

end OAI
