import Mathlib.Logic.Equiv.Prod
import OAI.Combinatorics.Progressions.Estimates.FiniteBiasedSlice

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def matrixCoordinateSplit {H I : Type*} [DecidableEq I]
    (j : H → I) (X : I → Type*) :
    (H → ∀ k, X k) ≃ (∀ i, X (j i)) × (∀ i, ∀ k : {k // k ≠ j i}, X k) where
  toFun v := (fun i => v i (j i), fun i k => v i k)
  invFun p i := (Equiv.piSplitAt (j i) X).symm (p.1 i, p.2 i)
  left_inv v := by
    funext i
    exact (Equiv.piSplitAt (j i) X).symm_apply_apply (v i)
  right_inv p := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst ((Equiv.piSplitAt (j i) X).apply_symm_apply (p.1 i, p.2 i))
    · funext i
      exact congrArg Prod.snd ((Equiv.piSplitAt (j i) X).apply_symm_apply (p.1 i, p.2 i))

theorem matrixCoordinateSplit_symm_update {H I : Type*} [DecidableEq I]
    (j : H → I) (X : I → Type*) (x x₀ : ∀ i, X (j i))
    (r : ∀ i, ∀ k : {k // k ≠ j i}, X k) :
    (matrixCoordinateSplit j X).symm (x, r) =
      fun i => Function.update ((matrixCoordinateSplit j X).symm (x₀, r) i) (j i) (x i) := by
  funext i k
  by_cases hk : k = j i
  · subst k
    simp [matrixCoordinateSplit, Equiv.piSplitAt]
  · simp [matrixCoordinateSplit, Equiv.piSplitAt, hk]

theorem exists_biased_matrix_coordinate_slice {H I : Type*} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I]
    (X : I → Type*) [∀ k, Fintype (X k)] [∀ k, Nonempty (X k)]
    (j : H → I) (F : (H → ∀ k, X k) → ℂ) {δ : ℝ}
    (hδ : δ ≤ ‖𝔼 v, F v‖) :
    ∃ b : H → ∀ k, X k, δ ≤ ‖𝔼 x : ∀ i, X (j i),
      F (fun i => Function.update (b i) (j i) (x i))‖ := by
  let e := matrixCoordinateSplit j X
  have he := Fintype.expect_equiv e F (fun p => F (e.symm p)) (fun v => by simp)
  rw [he, ← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm] at hδ
  obtain ⟨r, hr⟩ := exists_biased_finite_slice (fun r x => F (e.symm (x, r))) hδ
  let x₀ : ∀ i, X (j i) := fun i => Classical.choice inferInstance
  refine ⟨e.symm (x₀, r), ?_⟩
  have hmean : (𝔼 x : ∀ i, X (j i), F (e.symm (x, r))) =
      𝔼 x : ∀ i, X (j i), F (fun i => Function.update (e.symm (x₀, r) i) (j i) (x i)) := by
    apply Finset.expect_congr rfl
    intro x _
    exact congrArg F (matrixCoordinateSplit_symm_update j X x x₀ r)
  exact hr.trans_eq (congrArg norm hmean)

end Erdos3

end

end OAI
