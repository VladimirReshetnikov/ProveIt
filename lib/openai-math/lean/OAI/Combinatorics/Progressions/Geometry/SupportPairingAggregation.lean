import OAI.Combinatorics.Progressions.Linear.KernelSupportContraction

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productCouplingPairing_truncation_abs_le
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (D : Finset (Finset ι)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hprod : ∀ S ∈ D, (∏ i ∈ S, C i) ≤ ρ ^ 2)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
        ρ * Real.sqrt (productANOVAEnergy μ D w) * Real.sqrt (productANOVAEnergy ν D f) := by
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have ha (S : Finset ι) : 0 ≤ (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S w x ^ 2) :=
    FiniteProbabilityWeights.mean_nonneg _ (fun x => sq_nonneg (productANOVA μ S w x))
  have hb (S : Finset ι) : 0 ≤ (FiniteProbabilityWeights.pi ν).mean (fun x => productANOVA ν S f x ^ 2) :=
    FiniteProbabilityWeights.mean_nonneg _ (fun x => sq_nonneg (productANOVA ν S f x))
  have hpoint (S : Finset ι) (hS : S ∈ D) :
      productCouplingPairing c (productANOVA μ S w) (productANOVA ν S f) ^ 2 ≤
        (ρ ^ 2 * (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S w x ^ 2)) *
          (FiniteProbabilityWeights.pi ν).mean (fun x => productANOVA ν S f x ^ 2) :=
    (productCouplingPairing_support_sq_le μ ν K C hC hbound hK S w f).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hprod S hS) (ha S)) (hb S))
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul D
    (fun S _ => mul_nonneg (sq_nonneg ρ) (ha S)) (fun S _ => hb S) hpoint
  rw [← Finset.mul_sum] at hs
  change (∑ S ∈ D, productCouplingPairing c (productANOVA μ S w) (productANOVA ν S f)) ^ 2 ≤
    ρ ^ 2 * productANOVAEnergy μ D w * productANOVAEnergy ν D f at hs
  rw [productCouplingPairing_truncation]
  calc
    _ = Real.sqrt ((∑ S ∈ D, productCouplingPairing c (productANOVA μ S w) (productANOVA ν S f)) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (ρ ^ 2 * productANOVAEnergy μ D w * productANOVAEnergy ν D f) := Real.sqrt_le_sqrt hs
    _ = _ := by
      rw [Real.sqrt_mul (mul_nonneg (sq_nonneg ρ) (productANOVAEnergy_nonneg μ D w)),
        Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ]

end Erdos3

end

end OAI
