import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin

/-!
# The Vandermonde alternant

`det (y_i^{j})_{i,j < m} = ∏_{i<j} (y_j - y_i)` over every commutative ring, in Mathlib's
form `Matrix.det_vandermonde`; the alternant `a_δ(x) = ∏_{i<j} (x_i - x_j)` is the same
determinant with the sign `(-1)^{C(m,2)}` absorbed by reversing each factor.

## Main declarations

* `det_vandermonde_eq_prod`: the determinant formula.
* `prod_sub_eq_neg_one_pow_mul_det_vandermonde`: the alternant orientation `∏_{i<j} (x_i - x_j)`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset Matrix

variable {R : Type*} [CommRing R]

/-- **Vandermonde**: `det (y_i^j) = ∏_{i<j} (y_j - y_i)`. -/
theorem det_vandermonde_eq_prod {m : ℕ} (y : Fin m → R) :
    (vandermonde y).det = ∏ i : Fin m, ∏ j ∈ Ioi i, (y j - y i) :=
  det_vandermonde y

/-- `∑_{i<m} #{j > i} = C(m,2)`. -/
theorem sum_card_Ioi_fin (m : ℕ) : ∑ i : Fin m, (Ioi i).card = m.choose 2 := by
  simp_rw [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m, sum_range_reflect (fun i => i) m,
    sum_range_id, Nat.choose_two_right]

/-- The alternant orientation: `∏_{i<j} (y_i - y_j) = (-1)^{C(m,2)} det (y_i^j)`. -/
theorem prod_sub_eq_neg_one_pow_mul_det_vandermonde {m : ℕ} (y : Fin m → R) :
    ∏ i : Fin m, ∏ j ∈ Ioi i, (y i - y j) = (-1) ^ m.choose 2 * (vandermonde y).det := by
  rw [det_vandermonde]
  have h : ∀ i : Fin m, ∏ j ∈ Ioi i, (y i - y j) =
      (-1) ^ (Ioi i).card * ∏ j ∈ Ioi i, (y j - y i) := by
    intro i
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ => by ring
  simp_rw [h]
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, sum_card_Ioi_fin]

end Fabius
