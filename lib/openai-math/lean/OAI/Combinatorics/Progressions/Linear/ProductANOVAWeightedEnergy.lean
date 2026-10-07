import OAI.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_weighted_energy_le_lp (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (D : Finset (Finset I))
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1) :
    productANOVAEnergy μ D (fun x => rho x * F x) ≤
      finiteWeightedLp (fun x => (FiniteProbabilityWeights.pi μ).weight x * rho x) p F *
        finiteWeightedLp (fun x => (FiniteProbabilityWeights.pi μ).weight x * rho x) q
          (productANOVATruncation μ D (fun x => rho x * F x)) := by
  let P := productANOVATruncation μ D (fun x => rho x * F x)
  rw [productANOVAEnergy_pairing]
  have he : (FiniteProbabilityWeights.pi μ).mean (fun x => (rho x * F x) * P x) =
      ∑ x, ((FiniteProbabilityWeights.pi μ).weight x * rho x) * (F x * P x) := by
    unfold FiniteProbabilityWeights.mean
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  exact (le_abs_self _).trans (finiteWeightedHolder_pair _
    (fun x => mul_nonneg ((FiniteProbabilityWeights.pi μ).nonneg x) (hrho x)) p q hp hq hpq F P)

end Erdos3

end

end OAI
