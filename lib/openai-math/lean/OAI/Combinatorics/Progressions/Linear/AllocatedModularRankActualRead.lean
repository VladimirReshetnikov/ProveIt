import OAI.Combinatorics.Progressions.Polynomial.AllocatedModularRankTaggedPolynomials

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

theorem extend_selected_original {A K R : Type*} (slot : A → K)
    (hinj : Function.Injective slot) (c : K → R) :
    Function.extend slot (fun a => c (slot a)) c = c := by
  funext k
  by_cases hk : k ∈ Set.range slot
  · obtain ⟨a,rfl⟩ := hk
    exact hinj.extend_apply _ _ a
  · exact Function.extend_apply' _ _ k hk

namespace VectorPolynomial
variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedSelectedRankCoefficients
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N
  | .inl x, l => noise (spatialKernelRankSlot spatial l,x.val)
  | .inr (.inl i), l => r j (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel l) i
  | .inr (.inr a), l => projection a
      (canonicalPrincipalSubblockSlot (layerSamplerDegree I n) ⟨j,a.val⟩ (block a) l)

noncomputable def allocatedOriginalTaggedTop
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)
  | .inl x => homogeneousComponent 1
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (spatialRankPolynomial (fun d => noise (d,x.val))))
  | .inr (.inl i) => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v (modularDeckPolynomial r j i))
  | .inr (.inr a) => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1) (projection a)))

theorem allocatedTaggedRankPolynomial_original
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    allocatedTaggedRankPolynomial inactive j noise r projection spatial kernel block
      (allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block) v o =
        allocatedOriginalTaggedTop inactive j noise r projection v o := by
  rcases o with x | i | a
  · have hs : allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (.inl x) = fun l => noise (spatialKernelRankSlot spatial l,x.val) := by
      funext l
      rfl
    simp only [allocatedTaggedRankPolynomial, allocatedOriginalTaggedTop, hs]
    rw [extend_selected_original _ (spatialKernelRankSlot_injective spatial) (fun d => noise (d,x.val))]
  · have hs : allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (.inr (.inl i)) = fun l => r j (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel l) i := by
      funext l
      rfl
    simp only [allocatedTaggedRankPolynomial, allocatedDegreeRankPolynomial,
      allocatedOriginalTaggedTop, modularDeckPolynomial, resampleCoefficientDeckCoordinate_apply, hs]
    rw [extend_selected_original _ (kernelRankCoefficientSlot_injective
      (layerSamplerDegree I n) kernel (Nat.zero_lt_succ _)) (fun q => r j q i)]
  · have hs : allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (.inr (.inr a)) = fun l => projection a
          (canonicalPrincipalSubblockSlot (layerSamplerDegree I n) ⟨j,a.val⟩ (block a) l) := by
      funext l
      rfl
    simp only [allocatedTaggedRankPolynomial, allocatedDegreeRankPolynomial,
      allocatedOriginalTaggedTop, hs]
    exact congrArg
      (fun coefficients : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N =>
        homogeneousComponent (j.val + 1)
          (conditionPolynomial (allocatedLongEmbedding inactive)
            (allocatedLongEmbedding inactive).injective v
            (modularBoundedCoefficientPolynomial (j.val + 1) coefficients)))
      (extend_selected_original _ (canonicalPrincipalSubblockSlot_injective
        (G := G) (layerSamplerDegree I n) ⟨j,a.val⟩ (Nat.zero_lt_succ _) (block a)) (projection a))

theorem allocatedOriginalTaggedTop_eq_designated
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    allocatedOriginalTaggedTop inactive j noise r projection v o =
      designatedVectorComponent (allocatedTaggedRankBlock inactive j spatial kernel block)
        (allocatedTaggedRankResidual inactive j noise r projection spatial kernel block)
        (allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block) o := by
  rw [← allocatedTaggedRankPolynomial_original inactive j noise r projection spatial kernel block v o]
  exact allocatedTaggedRankPolynomial_eq_designated inactive j noise r projection spatial kernel block _ v o

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    {N L : ℕ}

theorem allocatedSelectedRankCoefficients_read
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (f : AllocatedActualCoefficientIndex G X I E n B → ZMod N)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedTaggedRankOutput X E inactive j) (l : Fin L) :
    allocatedSelectedRankCoefficients inactive j (allocatedReadNoise f) (allocatedReadDeck f)
      (fun a => allocatedReadProjection f ⟨j, a.val⟩) spatial (kernel j) (block j) o l =
      f (allocatedActualCoefficientSlot inactive spatial kernel block ⟨j, o, l⟩) := by
  rcases o with x | i | a <;> rfl

theorem allocatedSelectedRankCoefficients_read_function
    (inactive : LayerSamplerAxis I n → Prop)
    (f : AllocatedActualCoefficientIndex G X I E n B → ZMod N)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩) :
    (fun t : AllocatedSelectedCoefficientIndex X E inactive L =>
      allocatedSelectedRankCoefficients inactive t.1 (allocatedReadNoise f) (allocatedReadDeck f)
        (fun a => allocatedReadProjection f ⟨t.1, a.val⟩) spatial (kernel t.1) (block t.1) t.2.1 t.2.2) =
      f ∘ allocatedActualCoefficientSlot inactive spatial kernel block := by
  funext t
  exact allocatedSelectedRankCoefficients_read inactive t.1 f spatial kernel block t.2.1 t.2.2

end Erdos3.VectorPolynomial

end

end OAI
