import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Basis.VectorSpace
import OAI.Combinatorics.Progressions.Linear.WeightedLinearBaseProjection

namespace OAI

section

namespace Erdos3

open MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def coordinateWeightProjection (w : σ → ℕ) (n : ℕ) :
    (σ → ℚ) →ₗ[ℚ] (σ → ℚ) where
  toFun x i := if w i = n then x i else 0
  map_add' x y := by funext i; by_cases hi : w i = n <;> simp [hi]
  map_smul' r x := by funext i; by_cases hi : w i = n <;> simp [hi]

noncomputable def weightedLinearLeftInverse
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ) :
    (σ → ℚ) →ₗ[ℚ] (τ → ℚ) where
  toFun x j := A.leftInverse (coordinateWeightProjection w (v j) x) j
  map_add' x y := by funext j; simp only [map_add, Pi.add_apply]
  map_smul' r x := by funext j; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

omit [Fintype σ] in
theorem weightedLinearLeftInverse_apply [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hA : Function.Injective A) (x : τ → ℚ) :
    weightedLinearLeftInverse A v w (A x) = x := by
  funext j
  change A.leftInverse (fun i => if w i = v j then A x i else 0) j = x j
  rw [← linearMap_coordinateGradeProjection A v w hweight,
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hA)]
  simp

omit [Fintype σ] [Fintype τ] in
theorem weightedLinearLeftInverse_weighted [DecidableEq σ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (i : σ) (j : τ) (hij : w i ≠ v j) :
    weightedLinearLeftInverse A v w (Pi.single i 1) j = 0 := by
  change A.leftInverse (fun k => if w k = v j then (Pi.single i (1 : ℚ) : σ → ℚ) k else 0) j = 0
  have hzero : (fun k => if w k = v j then (Pi.single i (1 : ℚ) : σ → ℚ) k else 0) = 0 := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [hij]
    · simp [Pi.single_eq_of_ne hk]
  rw [hzero, map_zero]
  rfl

theorem polynomialLinearRestriction_leftInverse
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (B : (σ → ℚ) →ₗ[ℚ] (τ → ℚ))
    (hBA : ∀ x, B (A x) = x) (V : MvPolynomial τ ℚ) :
    polynomialLinearRestriction A (polynomialLinearRestriction B V) = V := by
  apply MvPolynomial.funext
  intro x
  rw [eval_polynomialLinearRestriction, eval_polynomialLinearRestriction, hBA]

theorem exists_weighted_polynomial_extension [DecidableEq σ] [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (hA : Function.Injective A) {d : ℕ} (V : MvPolynomial τ ℚ)
    (hV : V.IsWeightedHomogeneous v d) :
    ∃ W : MvPolynomial σ ℚ, W.IsWeightedHomogeneous w d ∧ polynomialLinearRestriction A W = V := by
  let B := weightedLinearLeftInverse A v w
  refine ⟨polynomialLinearRestriction B V, ?_, ?_⟩
  · exact polynomialLinearRestriction_isWeightedHomogeneous B w v
      (weightedLinearLeftInverse_weighted A v w) hV
  · exact polynomialLinearRestriction_leftInverse A B
      (weightedLinearLeftInverse_apply A v w hweight hA) V

end Erdos3

end

end OAI
