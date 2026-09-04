import FabiusFunction.BellGeneratingFunctions
import FabiusFunction.CoefficientRules

/-!
# The coefficients of `exp` of a power series

The recurrence the transseries volume writes at `p1:eq:g-recurrence`,

`g_0 = 1`,   `r g_r = ∑_{m=1}^{r} m κ_m g_{r-m}`   where `exp(∑ κ_m v^m) = ∑ g_r v^r`,

for an arbitrary power series `K` without constant term over a commutative
`ℚ`-algebra.  It is the coefficient form of `G' = K' G`, which is what
`derivative_subst` and `derivative_exp` give at once; the work is in the
reindexing, since the natural coefficient of a product runs the convolution the
other way round.

Two forms are supplied.  `succ_mul_expCoeff_succ` is the raw convolution, in
the shape the Cauchy product produces, and `natCast_mul_expCoeff` is the
volume's, summing `m κ_m g_{n-m}` over `m`.  The latter is stated over
`range (n+1)` rather than `Icc 1 n`, which costs nothing because the `m = 0`
term carries the factor `m` and vanishes; that also makes it true at `n = 0`,
where the volume's form would be an empty sum against `0 · g_0`.

Nothing here is specific to the gamma-ratio coefficients that motivate it: `K`
is any series with `constantCoeff K = 0`, so this is the general statement that
the coefficients of `exp(K)` are determined by those of `K` through a first-order
recurrence with no divisions until the last step.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The coefficients `g_r` of `exp(K)`, for a series `K` without constant
term. -/
noncomputable def expCoeff (K : A⟦X⟧) (r : ℕ) : A := coeff r ((exp A).subst K)

/-- `g_0 = 1`. -/
theorem expCoeff_zero {K : A⟦X⟧} (hK : constantCoeff K = 0) : expCoeff A K 0 = 1 := by
  rw [expCoeff, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_subst_of_constantCoeff_eq_zero A hK, constantCoeff_exp]

/-- **The recurrence, convolution form.**  `(r+1) g_{r+1} = ∑_{j ≤ r} g_j (r-j+1) κ_{r-j+1}`,
the coefficient of `z^r` in `G' = G K'`. -/
theorem succ_mul_expCoeff_succ {K : A⟦X⟧} (hK : constantCoeff K = 0) (r : ℕ) :
    ((r : A) + 1) * expCoeff A K (r + 1)
      = ∑ j ∈ range (r + 1),
          expCoeff A K j * (((r - j : ℕ) : A) + 1) * coeff (r - j + 1) K := by
  have hs : HasSubst K := HasSubst.of_constantCoeff_zero' hK
  have hD : d⁄dX A ((exp A).subst K) = (exp A).subst K * d⁄dX A K := by
    rw [derivative_subst A hs, derivative_exp]
  have h := congrArg (coeff r) hD
  rw [coeff_derivative_eq, coeff_mul_eq_sum_range] at h
  rw [expCoeff, h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_derivative_eq, expCoeff, mul_assoc]

/-- **`p1:eq:g-recurrence`.**  `n g_n = ∑_{m ≤ n} m κ_m g_{n-m}`, the volume's form.
The `m = 0` term vanishes because of its factor `m`, so summing from `0` rather
than from `1` costs nothing and makes the statement true at `n = 0` as well. -/
theorem natCast_mul_expCoeff {K : A⟦X⟧} (hK : constantCoeff K = 0) (n : ℕ) :
    (n : A) * expCoeff A K n
      = ∑ m ∈ range (n + 1), (m : A) * coeff m K * expCoeff A K (n - m) := by
  cases n with
  | zero => simp
  | succ r =>
      have hmain := succ_mul_expCoeff_succ A hK r
      have hreflect : ∑ i ∈ range (r + 1),
            ((i + 1 : ℕ) : A) * coeff (i + 1) K * expCoeff A K (r - i)
          = ∑ j ∈ range (r + 1),
            expCoeff A K j * (((r - j : ℕ) : A) + 1) * coeff (r - j + 1) K := by
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [Nat.sub_sub_self hjr]
        push_cast
        ring
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, add_zero, Nat.succ_sub_succ_eq_sub]
      rw [hreflect, ← hmain]
      push_cast
      ring

end Fabius
