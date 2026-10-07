import OAI.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder
import OAI.Combinatorics.Progressions.Probability.ProductEmbeddingConditional

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {X : I → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (e : J ↪ I) (base : ∀ i, X i)

include base

theorem productANOVA_embedding (S : Finset J) (f : (∀ j, X (e j)) → ℝ) (x : ∀ i, X i) :
    productANOVA μ (S.map e) (fun y => f (fun j => y (e j))) x =
      productANOVA (fun j => μ (e j)) S f (fun j => x (e j)) := by
  have happ (U : Finset J) : (Finset.mapEmbedding e).toEmbedding U = U.map e := rfl
  have hp : (S.map e).powerset = S.powerset.map (Finset.mapEmbedding e).toEmbedding := by
    simp only [Finset.map_eq_image, Finset.powerset_image]
    congr 1
    funext U
    exact (Finset.map_eq_image e U).symm
  unfold productANOVA
  rw [hp, Finset.sum_map]
  simp only [happ, Finset.card_map,
    ← Finset.map_sdiff, productConditionalMean_embedding μ e base]

theorem productANOVATruncation_embedding (D : Finset (Finset J)) (f : (∀ j, X (e j)) → ℝ)
    (x : ∀ i, X i) :
    productANOVATruncation μ (D.map (Finset.mapEmbedding e).toEmbedding) (fun y => f (fun j => y (e j))) x =
      productANOVATruncation (fun j => μ (e j)) D f (fun j => x (e j)) := by
  have happ (U : Finset J) : (Finset.mapEmbedding e).toEmbedding U = U.map e := rfl
  unfold productANOVATruncation
  rw [Finset.sum_map]
  simp only [happ, productANOVA_embedding μ e base]

theorem productANOVAEnergy_embedding (D : Finset (Finset J)) (f : (∀ j, X (e j)) → ℝ) :
    productANOVAEnergy μ (D.map (Finset.mapEmbedding e).toEmbedding) (fun y => f (fun j => y (e j))) =
      productANOVAEnergy (fun j => μ (e j)) D f := by
  have happ (U : Finset J) : (Finset.mapEmbedding e).toEmbedding U = U.map e := rfl
  unfold productANOVAEnergy
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro S _
  simp only [happ, productANOVA_embedding μ e base]
  exact productMean_pullback μ e e.injective base (fun y => productANOVA (fun j => μ (e j)) S f y ^ 2)

end Erdos3

end

end OAI
