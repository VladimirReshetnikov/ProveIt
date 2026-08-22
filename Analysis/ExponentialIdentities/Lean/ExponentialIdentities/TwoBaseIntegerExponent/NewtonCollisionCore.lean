import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Newton append and residue-collision core

This file checks the field algebra behind the fresh-collision denominator lemma in the
post-report closure audit.  The localization and valuation wrapper is deliberately left as
a paper argument.
-/

namespace LeanProofs.TwoBaseIntegerExponent
namespace NewtonCollisionCore

open Polynomial
open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F]

/-- The coefficient used to append one node to a Newton interpolant. -/
def appendCoeff (P W : F[X]) (s y : F) : F :=
  (y - P.eval s) / W.eval s

/-- Append one Newton term. -/
def appendPolynomial (P W : F[X]) (s y : F) : F[X] :=
  P + C (appendCoeff P W s y) * W

/-- The appended polynomial assumes the requested value at the new node. -/
theorem appendPolynomial_eval_new (P W : F[X]) (s y : F)
    (hW : W.eval s ≠ 0) :
    (appendPolynomial P W s y).eval s = y := by
  simp only [appendPolynomial, eval_add, eval_mul, eval_C, appendCoeff]
  field_simp
  ring

/-- Old interpolation values are preserved at every zero of the old node product. -/
theorem appendPolynomial_eval_old (P W : F[X]) (s y t : F)
    (hWt : W.eval t = 0) :
    (appendPolynomial P W s y).eval t = P.eval t := by
  simp [appendPolynomial, hWt]

/-- Reduction modulo a prime: a collision of nodes and a mismatch of values make the
new interpolation residual nonzero. -/
theorem residual_ne_zero_of_node_collision
    (P : F[X]) {s t yOld yNew : F}
    (hst : s = t) (hOld : P.eval t = yOld) (hMismatch : yNew ≠ yOld) :
    yNew - P.eval s ≠ 0 := by
  rw [hst, hOld]
  exact sub_ne_zero.mpr hMismatch

/-- Conversely, a vanishing new residual forces the values to agree at colliding nodes. -/
theorem value_eq_of_node_collision_of_residual_eq_zero
    (P : F[X]) {s t yOld yNew : F}
    (hst : s = t) (hOld : P.eval t = yOld)
    (hResidual : yNew - P.eval s = 0) :
    yNew = yOld := by
  rw [hst, hOld] at hResidual
  exact sub_eq_zero.mp hResidual

/-! ## Translation covariance of the barycentric top coefficient -/

/-- Barycentric formula for the top divided difference on `N+1` indexed nodes. -/
def barycentricTop (N : ℕ) (node value : Fin (N + 1) → F) : F :=
  ∑ i, value i /
    ∏ j ∈ (Finset.univ.erase i), (node i - node j)

private theorem scaledNodeDenominator (N : ℕ) (node : Fin (N + 1) → F)
    (c : F) (i : Fin (N + 1)) :
    (∏ j ∈ (Finset.univ.erase i), (c * node i - c * node j)) =
      c ^ N * ∏ j ∈ (Finset.univ.erase i), (node i - node j) := by
  simp_rw [show ∀ j : Fin (N + 1),
      c * node i - c * node j = c * (node i - node j) by
        intro j
        ring]
  rw [Finset.prod_mul_distrib]
  simp

/-- Scaling every node by `c` and every value by `r` scales the top divided
difference by `r / c^N`.  Distinctness is exposed through the nonzero barycentric
denominators. -/
theorem barycentricTop_scale (N : ℕ) (node value : Fin (N + 1) → F)
    (c r : F) (hc : c ≠ 0)
    (hden : ∀ i, (∏ j ∈ (Finset.univ.erase i), (node i - node j)) ≠ 0) :
    barycentricTop N (fun i ↦ c * node i) (fun i ↦ r * value i) =
      (r / c ^ N) * barycentricTop N node value := by
  unfold barycentricTop
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [scaledNodeDenominator]
  have hcpow : c ^ N ≠ 0 := pow_ne_zero _ hc
  have hdi := hden i
  field_simp

end

end NewtonCollisionCore
end LeanProofs.TwoBaseIntegerExponent
