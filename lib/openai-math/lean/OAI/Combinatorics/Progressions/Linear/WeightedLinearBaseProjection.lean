/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ τ : Type*} [Fintype τ] [DecidableEq τ]

theorem linearMap_coordinateGradeProjection
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (n : ℕ) (z : τ → ℚ) :
    A (fun j => if v j = n then z j else 0) =
      fun i => if w i = n then A z i else 0 := by
  classical
  funext i
  rw [← linearMap_apply_sum_coordinates A _ i]
  by_cases hi : w i = n
  · rw [ite_eq_left hi, ← linearMap_apply_sum_coordinates A z i]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : v j = n
    · rw [ite_eq_left hj]
    · rw [ite_eq_right hj, mul_zero, hweight j i (by omega), zero_mul]
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : v j = n
    · rw [ite_eq_left hj, hweight j i (by omega), zero_mul]
    · rw [ite_eq_right hj, mul_zero]

theorem linearMap_preserves_weighted_base_layer
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (n : ℕ) (z : τ → ℚ) (hz : ∀ j, v j < n → z j = 0) :
    ∀ i, w i < n → A z i = 0 := by
  classical
  intro i hi
  rw [← linearMap_apply_sum_coordinates A z i]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : v j = w i
  · rw [hz j (by omega), mul_zero]
  · rw [hweight j i hj, zero_mul]

theorem linearMap_coordinateGradeProjection_eq_self_iff
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hA : Function.Injective A) (n : ℕ) (z : τ → ℚ) :
    (fun i => if w i = n then A z i else 0) = A z ↔
      (fun j => if v j = n then z j else 0) = z := by
  rw [← linearMap_coordinateGradeProjection A v w hweight n z]
  exact hA.eq_iff

theorem linearMap_reflects_weighted_base_layer
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hA : Function.Injective A) (n : ℕ) (z : τ → ℚ)
    (hz : ∀ i, w i < n → A z i = 0) :
    ∀ j, v j < n → z j = 0 := by
  classical
  intro j hj
  have hout : (fun i => if w i = v j then A z i else 0) = 0 := by
    funext i
    by_cases hi : w i = v j
    · rw [ite_eq_left hi, hz i (by omega)]
      rfl
    · rw [ite_eq_right hi]
      rfl
  have hin : (fun k => if v k = v j then z k else 0) = 0 := by
    apply hA
    rw [linearMap_coordinateGradeProjection A v w hweight, hout, map_zero]
  have hh := congrFun hin j
  simpa only [ite_true, Pi.zero_apply] using hh

theorem linearMap_weighted_base_layer_iff
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hA : Function.Injective A) (n : ℕ) (z : τ → ℚ) :
    (∀ i, w i < n → A z i = 0) ↔ (∀ j, v j < n → z j = 0) :=
  ⟨linearMap_reflects_weighted_base_layer A v w hweight hA n z,
    linearMap_preserves_weighted_base_layer A v w hweight n z⟩

end Erdos3

end

end OAI
