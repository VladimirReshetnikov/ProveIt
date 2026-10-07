import OAI.Combinatorics.Progressions.Lattices.AllocatedModularRankIntegerDecay
import OAI.Combinatorics.Progressions.Sampling.SamplerSeparatedVariables

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

noncomputable def allocatedUnconditionedCongruenceIntegerPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ) :
    AllocatedCongruenceRankOutput X E inactive j →
      MvPolynomial (LayerSamplerVariables G I n B) ℤ
  | .inl x => C (base x.val) + spatialRankPolynomial (fun d => noise (d, x.val))
  | .inr (.inl i) => modularBoundedCoefficientPolynomial (j.val + 1) (fun q => r j q i)
  | .inr (.inr a) => modularBoundedCoefficientPolynomial (j.val + 1)
      (projection (allocatedCongruenceIntegerEmbedding inactive j a))

noncomputable def allocatedSeparatedCongruencePolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    MvPolynomial (LayerSamplerLongVariables inactive G B ⊕
      (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ :=
  rename (samplerSeparatedVariable inactive (layerSamplerDegree I n))
    (allocatedUnconditionedCongruenceIntegerPolynomial inactive j base noise r projection o)

variable (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j)

theorem allocatedUnconditionedCongruenceIntegerPolynomial_degree :
    (allocatedUnconditionedCongruenceIntegerPolynomial inactive j base noise r projection o).totalDegree ≤
      j.val + 1 := by
  rcases o with x | i | a
  · apply (totalDegree_add _ _).trans
    apply max_le
    · rw [totalDegree_C]
      exact Nat.zero_le _
    · exact (spatialRankPolynomial_degree _).trans (by omega)
  · exact modularBoundedCoefficientPolynomial_degree _ _
  · exact modularBoundedCoefficientPolynomial_degree _ _

theorem allocatedSeparatedCongruencePolynomial_degree :
    (allocatedSeparatedCongruencePolynomial inactive j base noise r projection o).totalDegree ≤
      j.val + 1 :=
  (totalDegree_rename_le _ _).trans
    (allocatedUnconditionedCongruenceIntegerPolynomial_degree inactive j base noise r projection o)

theorem allocatedUnconditionedCongruenceIntegerPolynomial_condition
    (v : LayerSamplerVariables G I n B → ℤ) :
    conditionPolynomial (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective v
      (allocatedUnconditionedCongruenceIntegerPolynomial inactive j base noise r projection o) =
      allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o := by
  rcases o with x | i | a <;> rfl

theorem allocatedSeparatedCongruencePolynomial_eval
    (long : LayerSamplerLongVariables inactive G B → ℤ)
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ) :
    MvPolynomial.eval (Sum.elim long raw)
      (allocatedSeparatedCongruencePolynomial inactive j base noise r projection o) =
      MvPolynomial.eval long (allocatedCongruenceIntegerPolynomial inactive j base noise r projection
        (samplerFrozenRaw (layerSamplerDegree I n) raw) o) := by
  rw [allocatedSeparatedCongruencePolynomial, eval_rename_samplerSeparatedVariable]
  rw [← allocatedUnconditionedCongruenceIntegerPolynomial_condition]
  rfl

theorem allocatedSeparatedCongruencePolynomial_integerLongOutput
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (N : ℕ) (long : LayerSamplerLongVariables inactive G B → ZMod N) :
    integerLongPolynomialOutput
      (allocatedSeparatedCongruencePolynomial inactive j base noise r projection) raw N long o =
      MvPolynomial.eval (fun k => ((long k).val : ℤ))
        (allocatedCongruenceIntegerPolynomial inactive j base noise r projection
          (samplerFrozenRaw (layerSamplerDegree I n) raw) o) :=
  allocatedSeparatedCongruencePolynomial_eval inactive j base noise r projection o _ raw

end Erdos3.VectorPolynomial

end

end OAI
