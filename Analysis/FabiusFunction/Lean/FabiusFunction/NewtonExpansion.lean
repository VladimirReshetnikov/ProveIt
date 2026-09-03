import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots

/-!
# Newton's forward-difference expansion of polynomials

For a polynomial `p` of degree at most `d` and the forward difference
`Δ p(x) = p(x+1) - p(x)`,

`p(x) = ∑_{k ≤ d} (Δ^k p)(0) · C(x, k) = ∑_{k ≤ d} (Δ^k p)(0)/k! · x^{\underline k}`.

Mathlib provides the Gregory–Newton formula for functions
(`shift_eq_sum_fwdDiff_iter`) and the vanishing of `Δ^k p` for `k > deg p`
(`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`); we combine them into the
evaluation form over any commutative ring and into the polynomial identity over
a field of characteristic zero.

## Main results

* `eval_natCast_eq_sum_choose_fwdDiff`: `p(m) = ∑_{k ≤ d} C(m,k) (Δ^k p)(0)`
  for natural numbers `m`, over any commutative ring.
* `newton_expansion`: `p = ∑_{k ≤ d} C((Δ^k p)(0)/k!) · descPochhammer k` in `K[X]`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

section CommRing

variable {R : Type*} [CommRing R]

/-- **Newton's forward-difference formula at natural numbers:** if `deg p ≤ d` then
`p(m) = ∑_{k ≤ d} C(m,k) · (Δ^k p)(0)` for every natural number `m`. -/
theorem eval_natCast_eq_sum_choose_fwdDiff (p : R[X]) {d : ℕ} (hd : p.natDegree ≤ d) (m : ℕ) :
    p.eval (m : R) = ∑ k ∈ Finset.range (d + 1),
      (m.choose k : R) * (fwdDiff (1 : R))^[k] p.eval 0 := by
  have h := shift_eq_sum_fwdDiff_iter (1 : R) p.eval m 0
  rw [zero_add, nsmul_one] at h
  have hz : ∀ k, d < k → (fwdDiff (1 : R))^[k] p.eval 0 = 0 := by
    intro k hk
    have := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := p) (n := k) (by omega)
    exact congrFun this 0
  have h1 : ∑ k ∈ Finset.range (m + 1), m.choose k • (fwdDiff (1 : R))^[k] p.eval 0
      = ∑ k ∈ Finset.range (m + d + 1), m.choose k • (fwdDiff (1 : R))^[k] p.eval 0 := by
    refine Finset.sum_subset ?_ ?_
    · exact Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega)
    · intro k _ hk'
      rw [Finset.mem_range, not_lt] at hk'
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_nsmul]
  have h2 : ∑ k ∈ Finset.range (d + 1), (m.choose k : R) * (fwdDiff (1 : R))^[k] p.eval 0
      = ∑ k ∈ Finset.range (m + d + 1), (m.choose k : R) * (fwdDiff (1 : R))^[k] p.eval 0 := by
    refine Finset.sum_subset ?_ ?_
    · exact Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega)
    · intro k _ hk'
      rw [Finset.mem_range, not_lt] at hk'
      rw [hz k (by omega), mul_zero]
  rw [h, h1, h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nsmul_eq_mul]

end CommRing

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- **Newton's expansion in the falling-factorial basis:** if `deg p ≤ d` then
`p = ∑_{k ≤ d} (Δ^k p)(0)/k! · x^{\underline k}` in `K[X]`. -/
theorem newton_expansion (p : K[X]) {d : ℕ} (hd : p.natDegree ≤ d) :
    p = ∑ k ∈ Finset.range (d + 1),
      C ((fwdDiff (1 : K))^[k] p.eval 0 / k.factorial) * descPochhammer K k := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m : K)) Nat.cast_injective
  intro m
  simp only [Set.mem_setOf_eq, eval_finsetSum, eval_mul, eval_C,
    descPochhammer_eval_eq_descFactorial]
  rw [eval_natCast_eq_sum_choose_fwdDiff p hd m]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  have hk : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  push_cast
  rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hk]
  ring

end Field

end Fabius
