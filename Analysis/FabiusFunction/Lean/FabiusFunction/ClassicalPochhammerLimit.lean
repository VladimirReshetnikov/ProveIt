import FabiusFunction.FiniteQBinomialCore
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The classical limit of finite q-Pochhammer symbols

For a parameter family `a = f(q)` with `f(1) = 1` and `f'(1) = c`, the finite
symbol `(f(q);q)_n`, divided by `(1-q)^n`, tends as `q → 1` to the classical
rising factorial `(c)_n = c (c+1) ⋯ (c+n-1)`:

`(f(q);q)_n / (1-q)^n = ∏_{j<n} (1 - f(q) q^j)/(1 - q) → ∏_{j<n} (c + j)`.

The only input is the derivative at `1` of each factor `q ↦ f(q) q^j`, which
is `c + j`: the quotient `(1 - f(q) q^j)/(1 - q)` is the difference quotient
of that factor at `1`.  Nothing else about `f` enters, and the field is
arbitrary.  Specializing to `f(q) = q^x` (complex powers with the principal
branch, or real powers) gives the classical limit `(q^x;q)_n/(1-q)^n → (x)_n`.

## Main declarations

* `tendsto_one_sub_div_one_sub_of_hasDerivAt`: `(1 - f(q))/(1 - q) → f'(1)`.
* `tendsto_finiteQPochhammerIn_div_pow_of_hasDerivAt`: the limit for every
  differentiable parameter family.
* `tendsto_finiteQPochhammerIn_cpow_div_pow`,
  `tendsto_finiteQPochhammerIn_rpow_div_pow`: the complex and real classical
  limits `(q^x;q)_n/(1-q)^n → (x)_n`.
* `ascPochhammer_eval_eq_prod_range`: `(x)_n = ∏_{j<n} (x + j)`.
-/

set_option autoImplicit false

open Filter Topology Polynomial
open scoped BigOperators

namespace Fabius

/-- The rising factorial as a product: `(x)_n = ∏_{j<n} (x + j)`. -/
theorem ascPochhammer_eval_eq_prod_range {S : Type*} [CommSemiring S] (n : ℕ) (x : S) :
    (ascPochhammer S n).eval x = ∏ j ∈ Finset.range n, (x + j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- If `f(1) = 1` and `f'(1) = c`, then `(1 - f(q))/(1 - q) → c` as `q → 1`,
`q ≠ 1`: the quotient is the difference quotient of `f` at `1`. -/
theorem tendsto_one_sub_div_one_sub_of_hasDerivAt {f : 𝕜 → 𝕜} {c : 𝕜}
    (hf : HasDerivAt f c 1) (hf1 : f 1 = 1) :
    Tendsto (fun q : 𝕜 => (1 - f q) / (1 - q)) (𝓝[≠] 1) (𝓝 c) := by
  refine (hasDerivAt_iff_tendsto_slope.mp hf).congr fun q => ?_
  rw [slope_def_field, hf1, ← neg_sub (f q) 1, ← neg_sub q 1, neg_div_neg_eq]

/-- **The classical limit for a differentiable parameter family.**  If
`f(1) = 1` and `f'(1) = c`, then `(f(q);q)_n / (1-q)^n → (c)_n` as `q → 1`,
`q ≠ 1`, in every nontrivially normed field. -/
theorem tendsto_finiteQPochhammerIn_div_pow_of_hasDerivAt {f : 𝕜 → 𝕜} {c : 𝕜}
    (hf : HasDerivAt f c 1) (hf1 : f 1 = 1) (n : ℕ) :
    Tendsto (fun q : 𝕜 => finiteQPochhammerIn (f q) q n / (1 - q) ^ n) (𝓝[≠] 1)
      (𝓝 ((ascPochhammer 𝕜 n).eval c)) := by
  have hfac : ∀ j : ℕ,
      Tendsto (fun q : 𝕜 => (1 - f q * q ^ j) / (1 - q)) (𝓝[≠] 1) (𝓝 (c + j)) := by
    intro j
    have hg : HasDerivAt (fun q : 𝕜 => f q * q ^ j) (c + j) 1 := by
      refine (hf.mul (hasDerivAt_pow j (1 : 𝕜))).congr_deriv ?_
      simp only [hf1, one_pow, mul_one, one_mul]
    exact tendsto_one_sub_div_one_sub_of_hasDerivAt hg (by simp [hf1])
  rw [ascPochhammer_eval_eq_prod_range]
  refine (tendsto_finset_prod (Finset.range n) fun j _ => hfac j).congr fun q => ?_
  rw [finiteQPochhammerIn, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]

/-- **The complex classical limit** `(q^x;q)_n / (1-q)^n → (x)_n` as `q → 1`,
`q ≠ 1`, with the principal branch of `q^x`. -/
theorem tendsto_finiteQPochhammerIn_cpow_div_pow (x : ℂ) (n : ℕ) :
    Tendsto (fun q : ℂ => finiteQPochhammerIn (q ^ x) q n / (1 - q) ^ n) (𝓝[≠] 1)
      (𝓝 ((ascPochhammer ℂ n).eval x)) := by
  have hd : HasDerivAt (fun q : ℂ => q ^ x) x 1 := by
    have h := (hasDerivAt_id (1 : ℂ)).cpow_const (c := x) (by simp)
    simpa using h
  exact tendsto_finiteQPochhammerIn_div_pow_of_hasDerivAt hd (Complex.one_cpow x) n

/-- **The real classical limit** `(q^x;q)_n / (1-q)^n → (x)_n` as `q → 1`,
`q ≠ 1`. -/
theorem tendsto_finiteQPochhammerIn_rpow_div_pow (x : ℝ) (n : ℕ) :
    Tendsto (fun q : ℝ => finiteQPochhammerIn (q ^ x) q n / (1 - q) ^ n) (𝓝[≠] 1)
      (𝓝 ((ascPochhammer ℝ n).eval x)) := by
  have hd : HasDerivAt (fun q : ℝ => q ^ x) x 1 := by
    have h := Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := x) (Or.inl one_ne_zero)
    simpa using h
  exact tendsto_finiteQPochhammerIn_div_pow_of_hasDerivAt hd (Real.one_rpow x) n

end Fabius
