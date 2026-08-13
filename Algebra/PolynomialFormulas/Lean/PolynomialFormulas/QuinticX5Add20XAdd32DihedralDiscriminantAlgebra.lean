import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic
import PolynomialFormulas.LazardQuinticF20Action
import PolynomialFormulas.QuinticX5Add20XAdd32DihedralFinite

/-!
# The Vandermonde algebra for a displayed five-root tuple

This module caches the only moderately expensive polynomial identity used by
the square-discriminant parity bridge.  Each derivative evaluation and each
upper-triangular Vandermonde product is normalized separately before the
final ring identity.
-/

open scoped BigOperators Polynomial
open Polynomial Equiv

namespace LeanProofs.PolynomialFormulas.QuinticX5Add20XAdd32Dihedral

open LazardQuintic

set_option autoImplicit false

/-- The determinant of the Vandermonde matrix of an ordered root tuple. -/
def rootDetDelta {K : Type*} [CommRing K] (x : Fin 5 → K) : K :=
  (Matrix.vandermonde x).det

/-- Ring homomorphisms commute with the Vandermonde determinant. -/
theorem map_rootDetDelta
    {K L : Type*} [CommRing K] [CommRing L] (phi : K →+* L)
    (x : Fin 5 → K) :
    phi (rootDetDelta x) = rootDetDelta (fun i => phi (x i)) := by
  rw [rootDetDelta, rootDetDelta, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.vandermonde_apply]

/-- Reordering the roots multiplies their Vandermonde determinant by the
sign of the reordering permutation. -/
theorem rootDetDelta_permute
    {K : Type*} [CommRing K] (x : Fin 5 → K) (g : Classification.S5) :
    rootDetDelta (permuteRootTuple x g) =
      (g.sign : K) * rootDetDelta x := by
  change (Matrix.vandermonde (x ∘ g)).det =
    (g.sign : K) * (Matrix.vandermonde x).det
  change ((Matrix.vandermonde x).submatrix g id).det =
    (g.sign : K) * (Matrix.vandermonde x).det
  exact Matrix.det_permute g (Matrix.vandermonde x)

/-! The upper-triangular products are kept as separate cheap declarations so
index-normalization failures are reported before any derivative expansion. -/

theorem prod_Ioi_zero_fin5
    {K : Type*} [CommMonoid K] (f : Fin 5 → K) :
    (∏ j ∈ Finset.Ioi (0 : Fin 5), f j) = f 1 * f 2 * f 3 * f 4 := by
  rw [Fin.prod_Ioi_zero, Fin.prod_univ_four]
  change f 1 * f 2 * f 3 * f 4 = _
  rfl

theorem prod_Ioi_one_fin5
    {K : Type*} [CommMonoid K] (f : Fin 5 → K) :
    (∏ j ∈ Finset.Ioi (1 : Fin 5), f j) = f 2 * f 3 * f 4 := by
  rw [show (1 : Fin 5) = (0 : Fin 4).succ by rfl,
    Fin.prod_Ioi_succ, Fin.prod_Ioi_zero, Fin.prod_univ_three]
  change f 2 * f 3 * f 4 = _
  rfl

theorem prod_Ioi_two_fin5
    {K : Type*} [CommMonoid K] (f : Fin 5 → K) :
    (∏ j ∈ Finset.Ioi (2 : Fin 5), f j) = f 3 * f 4 := by
  rw [show (2 : Fin 5) = (1 : Fin 4).succ by rfl,
    Fin.prod_Ioi_succ,
    show (1 : Fin 4) = (0 : Fin 3).succ by rfl,
    Fin.prod_Ioi_succ, Fin.prod_Ioi_zero, Fin.prod_univ_two]
  change f 3 * f 4 = _
  rfl

theorem prod_Ioi_three_fin5
    {K : Type*} [CommMonoid K] (f : Fin 5 → K) :
    (∏ j ∈ Finset.Ioi (3 : Fin 5), f j) = f 4 := by
  rw [show (3 : Fin 5) = (2 : Fin 4).succ by rfl,
    Fin.prod_Ioi_succ,
    show (2 : Fin 4) = (1 : Fin 3).succ by rfl,
    Fin.prod_Ioi_succ,
    show (1 : Fin 3) = (0 : Fin 2).succ by rfl,
    Fin.prod_Ioi_succ, Fin.prod_Ioi_zero, Fin.prod_univ_one]
  change f 4 = _
  rfl

theorem prod_Ioi_four_fin5
    {K : Type*} [CommMonoid K] (f : Fin 5 → K) :
    (∏ j ∈ Finset.Ioi (4 : Fin 5), f j) = 1 := by
  rw [show (4 : Fin 5) = (3 : Fin 4).succ by rfl,
    Fin.prod_Ioi_succ,
    show (3 : Fin 4) = (2 : Fin 3).succ by rfl,
    Fin.prod_Ioi_succ,
    show (2 : Fin 3) = (1 : Fin 2).succ by rfl,
    Fin.prod_Ioi_succ,
    show (1 : Fin 2) = (0 : Fin 1).succ by rfl,
    Fin.prod_Ioi_succ, Fin.prod_Ioi_zero, Fin.prod_univ_zero]

/-- The product of the derivatives at five displayed roots is the square of
their Vandermonde determinant. -/
theorem prod_eval_derivative_prod_X_sub_C_eq_rootDetDelta_sq
    {K : Type*} [Field K] (x : Fin 5 → K) :
    (∏ i : Fin 5,
        eval (x i) ((∏ j : Fin 5, (X - C (x j))).derivative)) =
      rootDetDelta x ^ 2 := by
  let P : K[X] := ∏ j : Fin 5, (X - C (x j))
  have h0 : eval (x 0) P.derivative =
      (x 0 - x 1) * (x 0 - x 2) * (x 0 - x 3) * (x 0 - x 4) := by
    simp only [P, Fin.prod_univ_five]
    simp [derivative_mul]
  have h1 : eval (x 1) P.derivative =
      (x 1 - x 0) * (x 1 - x 2) * (x 1 - x 3) * (x 1 - x 4) := by
    simp only [P, Fin.prod_univ_five]
    simp [derivative_mul]
  have h2 : eval (x 2) P.derivative =
      (x 2 - x 0) * (x 2 - x 1) * (x 2 - x 3) * (x 2 - x 4) := by
    simp only [P, Fin.prod_univ_five]
    simp [derivative_mul]
  have h3 : eval (x 3) P.derivative =
      (x 3 - x 0) * (x 3 - x 1) * (x 3 - x 2) * (x 3 - x 4) := by
    simp only [P, Fin.prod_univ_five]
    simp [derivative_mul]
  have h4 : eval (x 4) P.derivative =
      (x 4 - x 0) * (x 4 - x 1) * (x 4 - x 2) * (x 4 - x 3) := by
    simp only [P, Fin.prod_univ_five]
    simp [derivative_mul]
  have hi0 :
      (∏ j ∈ Finset.Ioi (0 : Fin 5), (x j - x 0)) =
        (x 1 - x 0) * (x 2 - x 0) * (x 3 - x 0) * (x 4 - x 0) := by
    exact prod_Ioi_zero_fin5 (fun j => x j - x 0)
  have hi1 :
      (∏ j ∈ Finset.Ioi (1 : Fin 5), (x j - x 1)) =
        (x 2 - x 1) * (x 3 - x 1) * (x 4 - x 1) := by
    exact prod_Ioi_one_fin5 (fun j => x j - x 1)
  have hi2 :
      (∏ j ∈ Finset.Ioi (2 : Fin 5), (x j - x 2)) =
        (x 3 - x 2) * (x 4 - x 2) := by
    exact prod_Ioi_two_fin5 (fun j => x j - x 2)
  have hi3 :
      (∏ j ∈ Finset.Ioi (3 : Fin 5), (x j - x 3)) = x 4 - x 3 := by
    exact prod_Ioi_three_fin5 (fun j => x j - x 3)
  have hi4 :
      (∏ j ∈ Finset.Ioi (4 : Fin 5), (x j - x 4)) = 1 := by
    exact prod_Ioi_four_fin5 (fun j => x j - x 4)
  change (∏ i : Fin 5, eval (x i) P.derivative) = rootDetDelta x ^ 2
  rw [Fin.prod_univ_five, h0, h1, h2, h3, h4, rootDetDelta,
    Matrix.det_vandermonde, Fin.prod_univ_five, hi0, hi1, hi2, hi3, hi4]
  ring

end LeanProofs.PolynomialFormulas.QuinticX5Add20XAdd32Dihedral
