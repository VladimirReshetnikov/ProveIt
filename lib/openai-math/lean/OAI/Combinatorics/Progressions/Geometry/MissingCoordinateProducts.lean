/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def missingCoordinateProduct {I K α : Type*} [Fintype I]
    (coordinate : I → K) (f : I → (K → α) → ℂ) (k : K) (x : K → α) : ℂ := by
  classical
  exact ∏ i ∈ Finset.univ with coordinate i = k, f i x

theorem missingCoordinateProduct_prod {I K α : Type*} [Fintype I] [Fintype K]
    (coordinate : I → K) (f : I → (K → α) → ℂ) (x : K → α) :
    (∏ k, missingCoordinateProduct coordinate f k x) = ∏ i, f i x := by
  classical
  exact Finset.prod_fiberwise Finset.univ coordinate (fun i => f i x)

theorem missingCoordinateProduct_norm {I K α : Type*} [Fintype I]
    (coordinate : I → K) (f : I → (K → α) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (k : K) (x : K → α) : ‖missingCoordinateProduct coordinate f k x‖ ≤ 1 := by
  classical
  unfold missingCoordinateProduct
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hf i x)

theorem missingCoordinateProduct_independent {I K α : Type*} [Fintype I]
    (coordinate : I → K) (f : I → (K → α) → ℂ)
    (hf : ∀ i x y, (∀ k, k ≠ coordinate i → x k = y k) → f i x = f i y)
    (k : K) (x y : K → α) (hxy : ∀ l, l ≠ k → x l = y l) :
    missingCoordinateProduct coordinate f k x = missingCoordinateProduct coordinate f k y := by
  classical
  apply Finset.prod_congr rfl
  intro i hi
  have heq : coordinate i = k := (Finset.mem_filter.mp hi).2
  apply hf i x y
  simpa only [heq] using hxy

theorem exists_missing_coordinate_product_factors {I K α : Type*} [Fintype I] [Fintype K]
    (f : I → (K → α) → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1)
    (hind : ∀ i, ∃ k, ∀ x y, (∀ l, l ≠ k → x l = y l) → f i x = f i y) :
    ∃ A : K → (K → α) → ℂ,
      (∀ k x, ‖A k x‖ ≤ 1) ∧
      (∀ k x y, (∀ l, l ≠ k → x l = y l) → A k x = A k y) ∧
      ∀ x, (∏ k, A k x) = ∏ i, f i x := by
  classical
  choose coordinate homit using hind
  exact ⟨missingCoordinateProduct coordinate f, missingCoordinateProduct_norm coordinate f hf,
    missingCoordinateProduct_independent coordinate f homit, missingCoordinateProduct_prod coordinate f⟩

end Erdos3

end

end OAI
