import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
import OAI.Combinatorics.Progressions.Linear.ModularVectorCoefficientRank

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedDegreeRankPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedDegreeRankOutput E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    AllocatedDegreeRankOutput E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl i => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularDeckPolynomial (resampleCoefficientDeckCoordinate r j i
          (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel) (c (.inl i))) j i))
  | .inr a => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1)
          (Function.extend (canonicalPrincipalSubblockSlot (layerSamplerDegree I n)
            ⟨j,a.val⟩ (block a)) (c (.inr a)) (projection a))))

noncomputable def allocatedDegreeRankResidual
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedDegreeRankOutput E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl i => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent (j.val + 1)
        (modularUnselectedCoefficientPolynomial (j.val + 1)
          (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel) (fun q => r j q i)))
  | .inr a => canonicalSelectedLongTopResidual inactive (layerSamplerDegree I n)
      (allocatedDegreeLongAxis inactive j a) (block a) (projection a)

theorem allocatedDegreeRankPolynomial_eq_designated
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedDegreeRankOutput E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedDegreeRankOutput E inactive j) :
    allocatedDegreeRankPolynomial inactive j r projection kernel block c v o =
      designatedVectorComponent (allocatedDegreeRankBlock inactive j kernel block)
        (allocatedDegreeRankResidual inactive j r projection kernel block) c o := by
  cases o with
  | inl i =>
    exact modularDeckPolynomial_kernel_resample_long_top inactive r j i kernel (c (.inl i)) v
  | inr a =>
    exact allocatedBoundedCoefficient_selected_long_top inactive
      (allocatedDegreeLongAxis inactive j a) (block a) (projection a) (c (.inr a)) v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedTaggedRankPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl x => homogeneousComponent 1
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (spatialRankPolynomial (Function.extend (spatialKernelRankSlot spatial)
          (c (.inl x)) (fun d => noise (d,x.val)))))
  | .inr o => allocatedDegreeRankPolynomial inactive j r projection kernel block
      (fun o => c (.inr o)) v o

noncomputable def allocatedTaggedRankResidual
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl x => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent 1
        (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range
          (spatialKernelRankSlot (P := PrincipalTupleIndex B (layerSamplerDegree I n)) spatial)),
          MvPolynomial.monomial (spatialRankExponent d) (noise (d,x.val))))
  | .inr o => allocatedDegreeRankResidual inactive j r projection kernel block o

theorem allocatedTaggedRankPolynomial_eq_designated
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    allocatedTaggedRankPolynomial inactive j noise r projection spatial kernel block c v o =
      designatedVectorComponent (allocatedTaggedRankBlock inactive j spatial kernel block)
        (allocatedTaggedRankResidual inactive j noise r projection spatial kernel block) c o := by
  cases o with
  | inl x =>
    have h := allocatedSpatialRankPolynomial_kernel_selected_long inactive spatial
      (fun d => noise (d,x.val)) (c (.inl x)) v
    simpa only [allocatedTaggedRankPolynomial, designatedVectorComponent,
      allocatedTaggedRankResidual, allocatedTaggedRankBlock,
      allocatedSpatialRankBlock_product] using h
  | inr o =>
    simpa only [allocatedTaggedRankPolynomial, designatedVectorComponent,
      allocatedTaggedRankBlock, allocatedTaggedRankResidual] using
      allocatedDegreeRankPolynomial_eq_designated inactive j r projection kernel block
        (fun o => c (.inr o)) v o

end Erdos3.VectorPolynomial

end

end OAI
