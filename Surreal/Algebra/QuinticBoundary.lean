import Surreal.Algebra.QuinticConstants

/-!
# Elementary witnesses and the complex collapse of the quintic

The x = 3 example and the algebraic counterexample mechanism from
`odg:def:rem:quintic`. The latter explains why ordering is indispensable.
-/

namespace Surreal.QuinticConstants

/-- The printed ordinary witnesses at x = 3. -/
theorem three_witness : value (3 : ℤ) 17 12 4 ![3, 2, 1, 1] = 0 := by
  norm_num [value, Fin.sum_univ_succ]

/-- A square root of -i*x produces a spurious quintic witness in a ring containing i. -/
theorem complex_collapse {R : Type*} [CommRing R] (x i s : R)
    (hi : i ^ 2 = -1) (hs : s ^ 2 = -i * x) : value x 1 0 1 ![i, s, 0, 0] = 0 := by
  have he : value x 1 0 1 ![i, s, 0, 0] = x ^ 3 * (1 + i ^ 2) := by
    simp only [value, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Finset.univ_eq_empty, Finset.sum_empty,
      zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, hi, hs]
    linear_combination x ^ 3 * hi
  rw [he, hi, add_neg_cancel, mul_zero]

end Surreal.QuinticConstants
