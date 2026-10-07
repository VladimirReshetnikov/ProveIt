import Mathlib.Algebra.MvPolynomial.Monad
import OAI.Combinatorics.Progressions.Estimates.StrideProductBounds

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

noncomputable def affineShiftCoordinate {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) (i : I) : MvPolynomial (Fin n) ℝ :=
  C (base i) + ∑ j, C (direction j i) * X j

noncomputable def affineShiftPullback {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) :
    MvPolynomial I ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  aeval (affineShiftCoordinate base direction)

theorem affineShiftPullback_eval {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (t : Fin n → ℝ) :
    eval t (affineShiftPullback base direction P) =
      eval (fun i => base i + ∑ j, direction j i * t j) P := by
  change (aeval t) ((aeval (affineShiftCoordinate base direction)) P) =
    (aeval (fun i => base i + ∑ j, direction j i * t j)) P
  rw [comp_aeval_apply]
  simp only [affineShiftCoordinate, map_add, map_sum, map_mul, aeval_C, aeval_X,
    Algebra.algebraMap_self_apply]

theorem affineShiftCoordinate_degree {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ) (i : I) :
    (affineShiftCoordinate base direction i).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp only [totalDegree_C, zero_le]
  · apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by simp)

theorem affineShiftPullback_degree {I : Type*} {n d : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ d) :
    (affineShiftPullback base direction P).totalDegree ≤ d := by
  simpa only [affineShiftPullback, aeval_eq_eval₂Hom, algebraMap_eq, Nat.mul_one] using polynomial_substitution_totalDegree_le P
    (affineShiftCoordinate base direction) (affineShiftCoordinate_degree base direction) hP

theorem affineShift_full_difference {I : Type*} {n : ℕ}
    (base : I → ℝ) (direction : Fin n → I → ℝ)
    (P : MvPolynomial I ℝ) (hP : P.totalDegree ≤ n) (u v : Fin n → ℝ) :
    additiveBoxDifference n
      (fun t (_ : Unit) => eval (fun i => base i + ∑ j, direction j i * t j) P) u v () =
      (affineShiftPullback base direction P).coeff (fullShiftExponent n) * ∏ i, (u i - v i) := by
  simpa only [affineShiftPullback_eval] using full_mixed_difference_of_totalDegree
    (affineShiftPullback base direction P) (affineShiftPullback_degree base direction P hP) u v

end Erdos3

end

end OAI
