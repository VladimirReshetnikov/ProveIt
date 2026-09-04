import FabiusFunction.ExponentialFormula

/-!
# Polynomial sequences of binomial type from complete Bell polynomials

For weights `a_1, a_2, …` put `p_n(x) = B_n(a_1 x, a_2 x, …) = ∑_k B_{n,k}(a) x^k`.
Then `p_n` is of binomial type,

`p_n(x + y) = ∑_{k ≤ n} C(n,k) p_k(x) p_{n-k}(y)`,

by the addition law of complete Bell polynomials, and its exponential
generating function is `exp(x h(t))` with `h(t) = ∑_j a_j t^j/j!`.

## Main results

* `binomialTypePoly`, `binomialTypePoly_eq_sum`, `binomialTypePoly_zero`.
* `binomialTypePoly_add`: the binomial identity.
* `exp_subst_smul_bellWeightSeries_eq_egfA_binomialTypePoly`: the generating function.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section

variable {R : Type*} [CommRing R]

/-- `p_n(x) = B_n(a_1 x, a_2 x, …)`, the binomial-type sequence attached to the
weights `a`. -/
noncomputable def binomialTypePoly (a : ℕ → R) (x : R) (n : ℕ) : R :=
  Bell.complete (fun j => a j * x) n

/-- `p_n(x) = ∑_{k ≤ n} B_{n,k}(a) x^k`. -/
theorem binomialTypePoly_eq_sum (a : ℕ → R) (x : R) (n : ℕ) :
    binomialTypePoly a x n = ∑ k ∈ Finset.range (n + 1), partialBell a n k * x ^ k := by
  rw [binomialTypePoly, bell_complete_eq_sum_partialBell]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : (fun j => a j * x) = fun j => x * a j := by
    funext j
    ring
  rw [h, partialBell_mul_left, mul_comm]

/-- `p_0 = 1`. -/
theorem binomialTypePoly_zero (a : ℕ → R) (x : R) : binomialTypePoly a x 0 = 1 := by
  rw [binomialTypePoly, Bell.complete_zero]

/-- **The binomial identity:** `p_n(x + y) = ∑_{k ≤ n} C(n,k) p_k(x) p_{n-k}(y)`. -/
theorem binomialTypePoly_add (a : ℕ → R) (x y : R) (n : ℕ) :
    binomialTypePoly a (x + y) n =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : R) * (binomialTypePoly a x k * binomialTypePoly a y (n - k)) := by
  have h : (fun j => a j * (x + y)) = (fun j => a j * x) + fun j => a j * y := by
    funext j
    simp only [Pi.add_apply]
    ring
  rw [binomialTypePoly, h, Bell.complete_add, Bell.binomialConv_eq_sum_range]
  rfl

/-- The binomial identity as an identity of sequences:
`p_·(x + y) = p_·(x) ⋆ p_·(y)` (binomial convolution). -/
theorem binomialTypePoly_add' (a : ℕ → R) (x y : R) :
    binomialTypePoly a (x + y) =
      Bell.binomialConv (binomialTypePoly a x) (binomialTypePoly a y) := by
  funext n
  have h : (fun j => a j * (x + y)) = (fun j => a j * x) + fun j => a j * y := by
    funext j
    simp only [Pi.add_apply]
    ring
  rw [binomialTypePoly, h, Bell.complete_add]
  rfl

/-! ### Sheffer sequences -/

/-- The Sheffer sequence `s_n(x) = ∑_k C(n,k) c_k p_{n-k}(x)` attached to the
coefficients `c` (of `g(t) = ∑ c_n t^n/n!`) and the binomial-type sequence of `a`. -/
noncomputable def shefferPoly (c a : ℕ → R) (x : R) : ℕ → R :=
  Bell.binomialConv c (binomialTypePoly a x)

/-- **The Sheffer addition law:** `s_n(x + y) = ∑_{k ≤ n} C(n,k) s_k(x) p_{n-k}(y)`. -/
theorem shefferPoly_add (c a : ℕ → R) (x y : R) (n : ℕ) :
    shefferPoly c a (x + y) n =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : R) * (shefferPoly c a x k * binomialTypePoly a y (n - k)) := by
  rw [shefferPoly, binomialTypePoly_add', ← Bell.binomialConv_assoc]
  exact Bell.binomialConv_eq_sum_range _ _ n

end

section EGF

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- **The generating function of a binomial-type sequence:**
`∑_n p_n(x) t^n/n! = exp(x h(t))` with `h(t) = ∑_{j ≥ 1} a_j t^j/j!`. -/
theorem exp_subst_smul_bellWeightSeries_eq_egfA_binomialTypePoly (a : ℕ → A) (x : A) :
    (exp A).subst (x • bellWeightSeries A a) = egfA A (binomialTypePoly a x) := by
  rw [exp_subst_smul_bellWeightSeries]
  congr 1
  funext n
  rw [binomialTypePoly_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The generating function of a Sheffer sequence:**
`∑_n s_n(x) t^n/n! = g(t) exp(x h(t))`. -/
theorem egfA_mul_exp_subst_smul_bellWeightSeries (c a : ℕ → A) (x : A) :
    egfA A c * (exp A).subst (x • bellWeightSeries A a) = egfA A (shefferPoly c a x) := by
  rw [exp_subst_smul_bellWeightSeries_eq_egfA_binomialTypePoly, egfA_mul]
  rfl

end EGF

end Fabius
