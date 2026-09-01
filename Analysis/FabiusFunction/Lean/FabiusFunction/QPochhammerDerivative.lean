import FabiusFunction.QPochhammerInfinite
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives of finite q-Pochhammer symbols in the parameter

The finite symbol `a ↦ (a;q)_n = ∏_{j<n} (1 - a q^j)` is a polynomial in `a`,
and the product rule gives its derivative as the sum over the factors:

`d/da (a;q)_n = -∑_{j<n} q^j ∏_{i<n, i≠j} (1 - a q^i)`.

Away from the zeros this is the logarithmic derivative

`(d/da (a;q)_n) / (a;q)_n = -∑_{j<n} q^j / (1 - a q^j)`,

and the chain rule transports both to a differentiable parameter `a(x)`.
Everything holds over every nontrivially normed field, with no hypothesis on
`q`.

## Main declarations

* `hasDerivAt_finiteQPochhammerIn`: the derivative as a sum of products.
* `hasDerivAt_finiteQPochhammerIn_of_ne_zero`: the logarithmic form.
* `hasDerivAt_finiteQPochhammerIn_comp`: the chain-rule form for `a = a(x)`.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The derivative of `a ↦ (a;q)_n`: `-∑_{j<n} q^j ∏_{i≠j} (1 - a q^i)`. -/
theorem hasDerivAt_finiteQPochhammerIn (q : 𝕜) (n : ℕ) (a : 𝕜) :
    HasDerivAt (fun a : 𝕜 => finiteQPochhammerIn a q n)
      (-∑ j ∈ Finset.range n, q ^ j * ∏ i ∈ (Finset.range n).erase j, (1 - a * q ^ i)) a := by
  have h : ∀ j ∈ Finset.range n, HasDerivAt (fun a : 𝕜 => 1 - a * q ^ j) (-(q ^ j)) a :=
    fun j _ => by simpa using ((hasDerivAt_id a).mul_const (q ^ j)).const_sub 1
  show HasDerivAt (fun a : 𝕜 => ∏ i ∈ Finset.range n, (1 - a * q ^ i)) _ a
  refine (HasDerivAt.fun_finsetProd h).congr_deriv ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul, mul_neg, mul_comm]

/-- **The logarithmic derivative** of `a ↦ (a;q)_n` away from its zeros:
`d/da (a;q)_n = -(a;q)_n ∑_{j<n} q^j/(1 - a q^j)`. -/
theorem hasDerivAt_finiteQPochhammerIn_of_ne_zero (q : 𝕜) (n : ℕ) {a : 𝕜}
    (ha : ∀ j ∈ Finset.range n, 1 - a * q ^ j ≠ 0) :
    HasDerivAt (fun a : 𝕜 => finiteQPochhammerIn a q n)
      (-(finiteQPochhammerIn a q n * ∑ j ∈ Finset.range n, q ^ j / (1 - a * q ^ j))) a := by
  refine (hasDerivAt_finiteQPochhammerIn q n a).congr_deriv ?_
  rw [neg_inj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hprod : finiteQPochhammerIn a q n =
      (1 - a * q ^ j) * ∏ i ∈ (Finset.range n).erase j, (1 - a * q ^ i) :=
    (Finset.mul_prod_erase (Finset.range n) (fun i => 1 - a * q ^ i) hj).symm
  have hc : (1 - a * q ^ j) * (1 - a * q ^ j)⁻¹ = 1 := mul_inv_cancel₀ (ha j hj)
  rw [hprod]
  linear_combination (-(q ^ j * ∏ i ∈ (Finset.range n).erase j, (1 - a * q ^ i))) * hc

/-- **Chain rule**: for a differentiable parameter `a(x)`,
`d/dx (a(x);q)_n = -a'(x) ∑_{j<n} q^j ∏_{i≠j} (1 - a(x) q^i)`. -/
theorem hasDerivAt_finiteQPochhammerIn_comp (q : 𝕜) (n : ℕ) {f : 𝕜 → 𝕜} {f' x : 𝕜}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x : 𝕜 => finiteQPochhammerIn (f x) q n)
      (-(f' * ∑ j ∈ Finset.range n, q ^ j * ∏ i ∈ (Finset.range n).erase j, (1 - f x * q ^ i))) x := by
  refine ((hasDerivAt_finiteQPochhammerIn q n (f x)).comp x hf).congr_deriv ?_
  ring

end Fabius
