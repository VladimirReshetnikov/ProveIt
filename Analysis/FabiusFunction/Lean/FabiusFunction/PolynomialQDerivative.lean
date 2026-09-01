import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Ring.GeomSum

/-!
# The q-derivative on polynomials

The Jackson `q`-derivative `D_q f(x) = (f(x) - f(qx)) / ((1-q)x)` is defined
here on polynomials over an arbitrary commutative semiring, coefficientwise
and division-free, in the same way as Mathlib's `Polynomial.derivative`:

`D_q (∑ a_n X^n) = ∑ a_n [n]_q X^{n-1}`, with `[n]_q = 1 + q + ⋯ + q^{n-1}`.

Its defining property is then the exact identity

`(1 - q) x · (D_q p)(x) = p(x) - p(qx)`,

valid in every commutative ring, with no division and no hypothesis on `q`.
The product rules `D_q(fg) = (D_q f) g + f(q·) (D_q g)` and the scaling rule
`D_q(f(c·)) = c (D_q f)(c·)` are proved by bilinearity from the monomial
case, where they reduce to the addition law `[m+n]_q = [m]_q + q^m [n]_q` of
`q`-integers.

## Main declarations

* `qInt`: the `q`-integer `[n]_q`, with `qInt_add`, `one_sub_mul_qInt`.
* `qDerivative`: the `q`-derivative as an `R`-linear map on `R[X]`.
* `qDerivative_monomial`, `qDerivative_X_pow`, `qDerivative_C`.
* `eval_qDerivative_mul`: the difference-quotient characterization.
* `qDerivative_mul`, `qDerivative_mul'`: the two product rules.
* `qDerivative_comp_C_mul_X`: the scaling rule.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

/-! ## q-integers -/

section QInt

variable {R : Type*} [Semiring R]

/-- The `q`-integer `[n]_q = 1 + q + ⋯ + q^{n-1}`. -/
def qInt (q : R) (n : ℕ) : R := ∑ i ∈ range n, q ^ i

@[simp] theorem qInt_zero (q : R) : qInt q 0 = 0 := by simp [qInt]

@[simp] theorem qInt_one (q : R) : qInt q 1 = 1 := by simp [qInt]

/-- `[n+1]_q = [n]_q + q^n`. -/
theorem qInt_succ (q : R) (n : ℕ) : qInt q (n + 1) = qInt q n + q ^ n := by
  simp [qInt, Finset.sum_range_succ]

/-- `[n+1]_q = 1 + q [n]_q`. -/
theorem qInt_succ' (q : R) (n : ℕ) : qInt q (n + 1) = 1 + q * qInt q n := by
  simp only [qInt, Finset.sum_range_succ', pow_zero, Finset.mul_sum, pow_succ']
  exact add_comm _ _

/-- The addition law of `q`-integers: `[m+n]_q = [m]_q + q^m [n]_q`. -/
theorem qInt_add (q : R) (m n : ℕ) : qInt q (m + n) = qInt q m + q ^ m * qInt q n := by
  simp only [qInt, Finset.sum_range_add, Finset.mul_sum, pow_add]

/-- At `q = 1` the `q`-integer is the integer. -/
@[simp] theorem qInt_one_left (n : ℕ) : qInt (1 : R) n = n := by simp [qInt]

end QInt

/-- `(1 - q) [n]_q = 1 - q^n`. -/
theorem one_sub_mul_qInt {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    (1 - q) * qInt q n = 1 - q ^ n :=
  mul_neg_geom_sum q n

/-! ## The q-derivative -/

section QDerivative

variable {R : Type*} [CommSemiring R]

/-- The `q`-derivative `D_q` on `R[X]`, coefficientwise:
`D_q (∑ a_n X^n) = ∑ a_n [n]_q X^{n-1}`. -/
noncomputable def qDerivative (q : R) : R[X] →ₗ[R] R[X] where
  toFun p := p.sum fun n a => C (a * qInt q n) * X ^ (n - 1)
  map_add' p₁ p₂ := by
    rw [sum_add_index] <;>
      simp only [add_mul, forall_const, RingHom.map_add, zero_mul, RingHom.map_zero]
  map_smul' a p := by
    dsimp
    rw [sum_smul_index] <;>
      simp only [mul_sum, ← C_mul', mul_assoc, RingHom.map_mul, forall_const,
        zero_mul, RingHom.map_zero, sum]

theorem qDerivative_apply (q : R) (p : R[X]) :
    qDerivative q p = p.sum fun n a => C (a * qInt q n) * X ^ (n - 1) := rfl

@[simp] theorem qDerivative_monomial (q : R) (n : ℕ) (a : R) :
    qDerivative q (monomial n a) = C (a * qInt q n) * X ^ (n - 1) := by
  rw [qDerivative_apply, sum_monomial_index]
  simp

@[simp] theorem qDerivative_C (q a : R) : qDerivative q (C a) = 0 := by
  rw [← monomial_zero_left, qDerivative_monomial]
  simp

@[simp] theorem qDerivative_X_pow (q : R) (n : ℕ) :
    qDerivative q (X ^ n) = C (qInt q n) * X ^ (n - 1) := by
  rw [← monomial_one_right_eq_X_pow, qDerivative_monomial, one_mul]

@[simp] theorem qDerivative_X (q : R) : qDerivative q X = 1 := by
  simpa using qDerivative_X_pow q 1

theorem qDerivative_C_mul_X_pow (q a : R) (n : ℕ) :
    qDerivative q (C a * X ^ n) = C (a * qInt q n) * X ^ (n - 1) := by
  rw [C_mul_X_pow_eq_monomial, qDerivative_monomial]

/-- **The difference-quotient characterization**, division-free:
`(1 - q) x · (D_q p)(x) = p(x) - p(qx)` in every commutative ring. -/
theorem eval_qDerivative_mul {S : Type*} [CommRing S] (q : S) (p : S[X]) (x : S) :
    (qDerivative q p).eval x * ((1 - q) * x) = p.eval x - p.eval (q * x) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ =>
      rw [map_add, eval_add, add_mul, h₁, h₂, eval_add, eval_add]
      ring
  | monomial n a =>
      rw [qDerivative_monomial, eval_mul, eval_C, eval_pow, eval_X, eval_monomial, eval_monomial]
      cases n with
      | zero => simp
      | succ n =>
          rw [Nat.add_sub_cancel, mul_pow]
          calc a * qInt q (n + 1) * x ^ n * ((1 - q) * x)
              = a * x ^ (n + 1) * ((1 - q) * qInt q (n + 1)) := by ring
            _ = a * x ^ (n + 1) - a * (q ^ (n + 1) * x ^ (n + 1)) := by
              rw [one_sub_mul_qInt]
              ring

/-- Scaling `p ↦ p(c·)` is `p.comp (C c * X)`; the `q`-derivative scales
accordingly: `D_q (p(c·)) = c · (D_q p)(c·)`. -/
theorem qDerivative_comp_C_mul_X (q c : R) (p : R[X]) :
    qDerivative q (p.comp (C c * X)) = C c * (qDerivative q p).comp (C c * X) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ => rw [add_comp, map_add, h₁, h₂, map_add, add_comp, mul_add]
  | monomial n a =>
      rw [monomial_comp, qDerivative_monomial, mul_comp, C_comp, pow_comp, X_comp]
      cases n with
      | zero => simp
      | succ n =>
          rw [Nat.add_sub_cancel, mul_pow, ← C_pow, ← mul_assoc, ← C_mul,
            qDerivative_C_mul_X_pow, Nat.add_sub_cancel, mul_pow, ← C_pow]
          simp only [C_mul, C_pow]
          ring

/-- **The product rule** `D_q(fg) = (D_q f) g + f(q·) (D_q g)`. -/
theorem qDerivative_mul (q : R) (f g : R[X]) :
    qDerivative q (f * g) = qDerivative q f * g + f.comp (C q * X) * qDerivative q g := by
  induction f using Polynomial.induction_on' with
  | add f₁ f₂ h₁ h₂ =>
      rw [add_mul, map_add, h₁, h₂, map_add, add_comp, add_mul, add_mul]
      ring
  | monomial m a => ?_
  induction g using Polynomial.induction_on' with
  | add g₁ g₂ h₁ h₂ =>
      rw [mul_add, map_add, h₁, h₂, map_add, mul_add, mul_add]
      ring
  | monomial n b => ?_
  rw [monomial_mul_monomial, qDerivative_monomial, qDerivative_monomial, qDerivative_monomial,
    monomial_comp]
  cases m with
  | zero =>
      simp only [zero_add, qInt_zero, mul_zero, map_zero, zero_mul, pow_zero, mul_one,
        ← C_mul_X_pow_eq_monomial, C_mul]
      ring
  | succ m =>
      cases n with
      | zero =>
          simp only [add_zero, qInt_zero, mul_zero, map_zero, zero_mul, pow_zero, mul_one,
            ← C_mul_X_pow_eq_monomial, Nat.add_sub_cancel, C_mul]
          ring
      | succ n =>
          rw [show m + 1 + (n + 1) - 1 = m + n + 1 by omega, Nat.add_sub_cancel,
            Nat.add_sub_cancel, ← C_mul_X_pow_eq_monomial, qInt_add]
          simp only [mul_pow, C_mul, C_pow, C_add]
          ring

/-- **The product rule, second form** `D_q(fg) = f (D_q g) + g(q·) (D_q f)`. -/
theorem qDerivative_mul' (q : R) (f g : R[X]) :
    qDerivative q (f * g) = f * qDerivative q g + g.comp (C q * X) * qDerivative q f := by
  rw [mul_comm f g, qDerivative_mul]
  ring

end QDerivative

end Fabius
