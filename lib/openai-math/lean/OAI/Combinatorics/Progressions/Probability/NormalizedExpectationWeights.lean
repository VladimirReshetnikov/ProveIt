import OAI.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def ofDensity {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (htotal : (𝔼 x, w x) = 1) : FiniteProbabilityWeights X where
  weight x := (Fintype.card X : ℝ)⁻¹ * w x
  nonneg x := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hw x)
  total := by
    rw [← Finset.mul_sum]
    simpa only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm] using htotal

theorem ofDensity_mean {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (htotal : (𝔼 x, w x) = 1) (f : X → ℝ) :
    (ofDensity w hw htotal).mean f = 𝔼 x, w x * f x := by
  simp only [mean, ofDensity, Fintype.expect_eq_sum_div_card, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem ofDensity_complexMean {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (htotal : (𝔼 x, w x) = 1) (f : X → ℂ) :
    (ofDensity w hw htotal).complexMean f = 𝔼 x, (w x : ℂ) * f x := by
  simp only [complexMean, ofDensity, Fintype.expect_eq_sum_div_card, div_eq_mul_inv,
    Finset.sum_mul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem reweight_mean {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : p.mean w = 1) (f : X → ℝ) :
    (p.reweight w hw htotal).mean f = p.mean (fun x => w x * f x) := by
  simp only [mean, reweight, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

end OAI
