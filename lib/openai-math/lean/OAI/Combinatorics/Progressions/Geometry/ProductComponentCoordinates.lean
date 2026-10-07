import OAI.Combinatorics.Progressions.Linear.TripleProductBasisBounds

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productFinBasis_repr_component (x : ∀ i, L i) (a : ι) (k : Fin (d a)) :
    (D a).basis.repr (x a) k =
      (pi D).basis.repr x (Fintype.equivFin (Σ i, Fin (d i)) ⟨a, k⟩) := by
  symm
  exact (productFinBasis_repr D x _).trans
    (congrArg (fun z : Σ i, Fin (d i) => (D z.1).basis.repr (x z.1) z.2)
      (Equiv.symm_apply_apply _ _))

theorem product_componentMap_logHeight {H κ : Type*} [LieRing H] [LieAlgebra ℚ H]
    (b : Basis κ ℚ H) (φ : H →ₗ⁅ℚ⁆ (∀ i, L i)) {p : ℝ}
    (hφ : ∀ i j, rationalLogHeight ((pi D).basis.repr (φ (b j)) i) ≤ p) :
    ∀ a i j, rationalLogHeight ((D a).basis.repr (((liePiEval a).comp φ) (b j)) i) ≤ p := by
  intro a i j
  change rationalLogHeight ((D a).basis.repr ((φ (b j)) a) i) ≤ p
  rw [productFinBasis_repr_component D]
  exact hφ _ j

end Erdos3.RationalFilteredNilmanifold

end

end OAI
