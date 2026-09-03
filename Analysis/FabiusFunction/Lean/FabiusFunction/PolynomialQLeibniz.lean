import FabiusFunction.PolynomialQDerivative
import FabiusFunction.QPascalSummation

/-!
# The q-Leibniz rule

Iterating the product rule `D_q(fg) = (D_q f) g + f(q·) (D_q g)` gives the
`q`-Leibniz rule

`D_q^n (fg) = ∑_{k=0}^{n} [n,k]_q (D_q^k f)(q^{n-k} ·) (D_q^{n-k} g)`,

on polynomials over every commutative semiring.  The inductive step is the
first `q`-Pascal summation `sum_gaussianBinomial_succ_mul`, read in the
polynomial ring; the scaling rule `D_q(p(c·)) = c (D_q p)(c·)` supplies the
weight `q^{n-k}` on the shifted term.

## Main declarations

* `comp_C_mul_X_comp_C_mul_X`: scalings compose multiplicatively.
* `qDerivative_C_mul`: `D_q` is linear over constants.
* `qDerivative_iterate_comp_C_mul_X`: the iterated scaling rule.
* `qDerivative_iterate_mul`: the `q`-Leibniz rule.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

variable {R : Type*} [CommSemiring R]

/-- Two scalings compose to the scaling by the product. -/
theorem comp_C_mul_X_comp_C_mul_X (p : R[X]) (c d : R) :
    (p.comp (C c * X)).comp (C d * X) = p.comp (C (c * d) * X) := by
  rw [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul]

/-- `D_q (C a * p) = C a * D_q p`. -/
theorem qDerivative_C_mul (q a : R) (p : R[X]) :
    qDerivative q (C a * p) = C a * qDerivative q p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul]

/-- The iterated scaling rule `D_q^k (p(c·)) = c^k (D_q^k p)(c·)`. -/
theorem qDerivative_iterate_comp_C_mul_X (q c : R) (p : R[X]) (k : ℕ) :
    (qDerivative q)^[k] (p.comp (C c * X)) =
      C (c ^ k) * ((qDerivative q)^[k] p).comp (C c * X) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, qDerivative_C_mul, qDerivative_comp_C_mul_X,
        Function.iterate_succ_apply', pow_succ, C_mul]
      ring

/-- **The `q`-Leibniz rule**
`D_q^n (fg) = ∑_k [n,k]_q (D_q^k f)(q^{n-k}·) (D_q^{n-k} g)`. -/
theorem qDerivative_iterate_mul (q : R) (f g : R[X]) (n : ℕ) :
    (qDerivative q)^[n] (f * g) =
      ∑ k ∈ range (n + 1), C (gaussianBinomial q n k) *
        (((qDerivative q)^[k] f).comp (C (q ^ (n - k)) * X) * (qDerivative q)^[n - k] g) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hL : (qDerivative q)^[n + 1] (f * g) = ∑ k ∈ range (n + 1),
          C (gaussianBinomial q n k) *
            (C (q ^ (n - k)) * (((qDerivative q)^[k + 1] f).comp (C (q ^ (n - k)) * X) *
                (qDerivative q)^[n - k] g) +
              ((qDerivative q)^[k] f).comp (C (q ^ (n + 1 - k)) * X) *
                (qDerivative q)^[n + 1 - k] g) := by
        rw [Function.iterate_succ_apply', ih, map_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hpow : q ^ (n - k) * q = q ^ (n + 1 - k) := by
          rw [← pow_succ]
          congr 1
          omega
        rw [qDerivative_C_mul, qDerivative_mul, qDerivative_comp_C_mul_X,
          comp_C_mul_X_comp_C_mul_X, ← Function.iterate_succ_apply' (qDerivative q) k f,
          ← Function.iterate_succ_apply' (qDerivative q) (n - k) g]
        simp only [Nat.succ_eq_add_one]
        rw [show n - k + 1 = n + 1 - k by omega, hpow]
        ring
      have hR := sum_gaussianBinomial_succ_mul (C q) n
        (fun k => ((qDerivative q)^[k] f).comp (C (q ^ (n + 1 - k)) * X) *
          (qDerivative q)^[n + 1 - k] g)
      beta_reduce at hR
      simp only [← map_gaussianBinomial C] at hR
      rw [hL, hR, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Nat.add_sub_add_right, ← C_pow]
      ring

end Fabius
