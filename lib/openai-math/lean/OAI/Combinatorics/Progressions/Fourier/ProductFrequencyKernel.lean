/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.NativeCentralSeed

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

noncomputable def piFrequency (eta : ∀ i, L i →ₗ[ℚ] ℚ) : (∀ i, L i) →ₗ[ℚ] ℚ :=
  ∑ i, (eta i).comp (liePiEval i).toLinearMap

theorem piFrequency_apply (eta : ∀ i, L i →ₗ[ℚ] ℚ) (x : ∀ i, L i) :
    piFrequency eta x = ∑ i, eta i (x i) := by
  simp only [piFrequency, LinearMap.sum_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    liePiEval_apply]

theorem piFrequency_single (eta : ∀ i, L i →ₗ[ℚ] ℚ) (i : ι) (x : L i) :
    letI := Classical.decEq ι
    piFrequency eta (Pi.single i x) = eta i x := by
  classical
  rw [piFrequency_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

theorem realify_piFrequency (eta : ∀ i, L i →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] (∀ i, L i)) :
    realifyFunctional (piFrequency eta) x =
      ∑ i, realifyFunctional (eta i) (realificationLieHom (liePiEval i) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realifyFunctional_tmul, piFrequency_apply, Rat.cast_sum,
      realificationLieHom_tmul, liePiEval_apply, Finset.mul_sum]
  | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib]

namespace RationalFilteredNilmanifold

variable {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem piFrequency_basis (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    piFrequency eta ((pi D).basis k) = eta z.1 ((D z.1).basis z.2) := by
  classical
  change piFrequency eta (productFinBasis D k) = _
  rw [productFinBasis, Basis.reindex_apply]
  generalize hz : (Fintype.equivFin (Σ i, Fin (d i))).symm k = z
  rcases z with ⟨i, j⟩
  rw [Pi.basis_apply, piFrequency_single]

theorem piFrequency_logHeight (eta : ∀ i, L i →ₗ[ℚ] ℚ) {p : ℝ}
    (hheight : ∀ i j, rationalLogHeight (eta i ((D i).basis j)) ≤ p)
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    rationalLogHeight (piFrequency eta ((pi D).basis k)) ≤ p := by
  rw [piFrequency_basis D]
  exact hheight _ _

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem realify_piFrequency_eq_component (eta : ∀ i, L i →ₗ[ℚ] ℚ) (i : ι)
    (x : ℝ ⊗[ℚ] (∀ i, L i))
    (hother : ∀ j, j ≠ i → realificationLieHom (liePiEval j) x = 0) :
    realifyFunctional (piFrequency eta) x =
      realifyFunctional (eta i) (realificationLieHom (liePiEval i) x) := by
  classical
  rw [realify_piFrequency, Finset.sum_eq_single i]
  · intro j _ hji
    rw [hother j hji, map_zero]
  · simp

theorem realify_component_zero_of_piFrequency_zero (eta : ∀ i, L i →ₗ[ℚ] ℚ) (i : ι)
    (x : ℝ ⊗[ℚ] (∀ i, L i)) (hzero : realifyFunctional (piFrequency eta) x = 0)
    (hother : ∀ j, j ≠ i → realificationLieHom (liePiEval j) x = 0) :
    realifyFunctional (eta i) (realificationLieHom (liePiEval i) x) = 0 := by
  rw [← realify_piFrequency_eq_component eta i x hother]
  exact hzero

end Erdos3

end

end OAI
