import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# The iterated Leibniz rule for formal power series

Over an arbitrary commutative ring,

`(d/dt)^n (f g) = ∑_{k ≤ n} C(n,k) f^{(k)} g^{(n-k)}`

(`derivative_iterate_mul`).  The combinatorial heart is Pascal's rule in convolution form,
`∑_{k ≤ n} C(n,k) T_{k+1} + ∑_{k ≤ n} C(n,k) T_k = ∑_{j ≤ n+1} C(n+1,j) T_j`
(`sum_pascal_split`), which is stated for an arbitrary sequence in a commutative ring and is
reusable for any two-term recurrence of binomial type.

## Main results

* `sum_pascal_split`.
* `derivative_natCast_mul`, `derivative_iterate_natCast_mul`, `derivative_iterate_mul`,
  `coeff_derivative_iterate_mul`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- **Pascal's rule in convolution form.**  For any sequence `T` in a commutative ring,
`∑_{k ≤ n} C(n,k) T_{k+1} + ∑_{k ≤ n} C(n,k) T_k = ∑_{j ≤ n+1} C(n+1,j) T_j`. -/
theorem sum_pascal_split {R : Type*} [CommRing R] (T : ℕ → R) (n : ℕ) :
    (∑ k ∈ range (n + 1), (n.choose k : R) * T (k + 1)) +
        ∑ k ∈ range (n + 1), (n.choose k : R) * T k =
      ∑ j ∈ range (n + 2), ((n + 1).choose j : R) * T j := by
  have hp : ∀ j ∈ range (n + 1),
      ((n + 1).choose (j + 1) : R) * T (j + 1) =
        (n.choose j : R) * T (j + 1) + (n.choose (j + 1) : R) * T (j + 1) := by
    intro j _
    rw [Nat.choose_succ_succ' n j, Nat.cast_add, add_mul]
  rw [Finset.sum_range_succ' (fun j => ((n + 1).choose j : R) * T j) (n + 1),
    Finset.sum_congr rfl hp, Finset.sum_add_distrib,
    Finset.sum_range_succ (fun j => (n.choose (j + 1) : R) * T (j + 1)) n,
    Finset.sum_range_succ' (fun k => (n.choose k : R) * T k) n]
  simp only [Nat.choose_succ_self, Nat.choose_zero_right, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul, add_zero]
  ring

variable (A : Type*) [CommRing A]

/-- A natural-number constant passes through `d/dt`. -/
theorem derivative_natCast_mul (m : ℕ) (f : A⟦X⟧) :
    d⁄dX A ((m : A⟦X⟧) * f) = (m : A⟦X⟧) * d⁄dX A f := by
  rw [Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero, smul_eq_mul]

/-- A natural-number constant passes through every iterate of `d/dt`. -/
theorem derivative_iterate_natCast_mul (m : ℕ) (f : A⟦X⟧) (n : ℕ) :
    (d⁄dX A)^[n] ((m : A⟦X⟧) * f) = (m : A⟦X⟧) * (d⁄dX A)^[n] f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, derivative_natCast_mul, ih,
      Function.iterate_succ_apply]

/-- **The iterated Leibniz rule:** `(d/dt)^n (f g) = ∑_{k ≤ n} C(n,k) f^{(k)} g^{(n-k)}`. -/
theorem derivative_iterate_mul (f g : A⟦X⟧) (n : ℕ) :
    (d⁄dX A)^[n] (f * g) =
      ∑ k ∈ range (n + 1), (n.choose k : A⟦X⟧) *
        ((d⁄dX A)^[k] f * (d⁄dX A)^[n - k] g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    have hterm : ∀ k ∈ range (n + 1),
        d⁄dX A ((n.choose k : A⟦X⟧) * ((d⁄dX A)^[k] f * (d⁄dX A)^[n - k] g)) =
          (n.choose k : A⟦X⟧) *
              ((d⁄dX A)^[k + 1] f * (d⁄dX A)^[n + 1 - (k + 1)] g) +
            (n.choose k : A⟦X⟧) * ((d⁄dX A)^[k] f * (d⁄dX A)^[n + 1 - k] g) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h1 : n + 1 - (k + 1) = n - k := by omega
      have h2 : n + 1 - k = n - k + 1 := by omega
      rw [derivative_natCast_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, h1, h2,
        ← Function.iterate_succ_apply' (d⁄dX A) k f,
        ← Function.iterate_succ_apply' (d⁄dX A) (n - k) g]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    exact sum_pascal_split (fun j => (d⁄dX A)^[j] f * (d⁄dX A)^[n + 1 - j] g) n

/-- The coefficient form of the iterated Leibniz rule. -/
theorem coeff_derivative_iterate_mul (f g : A⟦X⟧) (n m : ℕ) :
    coeff m ((d⁄dX A)^[n] (f * g)) =
      ∑ k ∈ range (n + 1), (n.choose k : A) *
        coeff m ((d⁄dX A)^[k] f * (d⁄dX A)^[n - k] g) := by
  rw [derivative_iterate_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_natCast (PowerSeries.C : A →+* A⟦X⟧), coeff_C_mul]

end Fabius
