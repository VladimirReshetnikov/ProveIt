import FabiusFunction.BellHomogeneity

/-!
# The exponential formula, bivariate form

With `C(z) = ∑_{j ≥ 1} x_j z^j/j!`, the exponential formula reads

`exp(u C(z)) = ∑_{n,k} B_{n,k}(x) u^k z^n/n!`,

whose specializations `u = 1` (`exp_subst_bellWeightSeries`) and the column
expansion `C(z)^k/k! = ∑_n B_{n,k} z^n/n!` (`bellWeightSeries_pow`) are proved
elsewhere.  The bivariate form follows from the degree homogeneity
`B_{n,k}(u x) = u^k B_{n,k}(x)`.

## Main results

* `bellWeightSeries_smul`, `exp_subst_smul_bellWeightSeries`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Scaling every weight by `u` scales the weight series by `u`. -/
theorem bellWeightSeries_smul (u : A) (x : ℕ → A) :
    bellWeightSeries A (fun j => u * x j) = u • bellWeightSeries A x := by
  ext n
  rw [bellWeightSeries, bellWeightSeries, PowerSeries.coeff_smul, coeff_egfA, coeff_egfA,
    smul_eq_mul]
  split_ifs <;> ring

/-- **The exponential formula, bivariate form:**
`exp(u C(z)) = ∑_n (∑_k B_{n,k}(x) u^k) z^n/n!`. -/
theorem exp_subst_smul_bellWeightSeries (u : A) (x : ℕ → A) :
    (exp A).subst (u • bellWeightSeries A x) =
      egfA A fun n => ∑ k ∈ Finset.range (n + 1), u ^ k * partialBell x n k := by
  rw [← bellWeightSeries_smul, exp_subst_bellWeightSeries]
  congr 1
  funext n
  rw [bell_complete_eq_sum_partialBell]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [partialBell_mul_left]

end Fabius
