/- Modified for ProveIt: define sum-indexed Lie instances by direct
constructor cases so their realifications reduce definitionally on Lean 4.32.
The public types and mathematical constructions are unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.ProductOrbitCongruence

namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

def sumLieSpace {ι κ : Type*} (L : ι → Type u) (M : κ → Type u) : ι ⊕ κ → Type u
  | .inl i => L i
  | .inr j => M j

instance sumLieRing {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)] (k : ι ⊕ κ) : LieRing (sumLieSpace L M k) :=
  match k with
  | .inl i => inferInstanceAs (LieRing (L i))
  | .inr j => inferInstanceAs (LieRing (M j))

instance sumLieAlgebra {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)] (k : ι ⊕ κ) :
    LieAlgebra ℚ (sumLieSpace L M k) :=
  match k with
  | .inl i => inferInstanceAs (LieAlgebra ℚ (L i))
  | .inr j => inferInstanceAs (LieAlgebra ℚ (M j))

instance sumRealificationTopology {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] (k : ι ⊕ κ) :
    TopologicalSpace (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] M j))

instance sumRealificationTopologicalAddGroup {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)]
    [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
    (k : ι ⊕ κ) : IsTopologicalAddGroup (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] M j))

instance sumRealificationContinuousSMul {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)]
    (k : ι ⊕ κ) : ContinuousSMul ℝ (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] M j))

instance sumRealificationT2Space {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)]
    [∀ i, T2Space (ℝ ⊗[ℚ] L i)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
    (k : ι ⊕ κ) : T2Space (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : T2Space (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : T2Space (ℝ ⊗[ℚ] M j))

namespace RationalFilteredNilmanifold

variable {ι κ σ : Type*} {L : ι → Type u} {M : κ → Type u}
  [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
  [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)] {s : ℕ} {d : ι → ℕ} {e : κ → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))

noncomputable def sumFactors : ∀ k : ι ⊕ κ,
    RationalFilteredNilmanifold (sumLieSpace L M k) s (Sum.elim d e k)
  | .inl i => D i
  | .inr j => E j

noncomputable def sumOrbits {w : σ → ℕ}
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w)
    (h : ∀ j, (E j).filtration.realification.PolynomialOrbit w) :
    ∀ k : ι ⊕ κ, (sumFactors D E k).filtration.realification.PolynomialOrbit w
  | .inl i => g i
  | .inr j => h j

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
