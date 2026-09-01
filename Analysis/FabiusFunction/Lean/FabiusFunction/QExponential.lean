import FabiusFunction.QBinomialTheoremInfinite
import FabiusFunction.PolynomialQTaylor

/-!
# The q-exponentials and the q-derivative of functions

Euler's two identities, read with `z = (1-q)x`, give the two `q`-exponentials

`e_q(x) = ∑ x^n/[n]_q! = 1/((1-q)x;q)_∞`  (`‖(1-q)x‖ < 1`),
`E_q(x) = ∑ q^{\binom n2} x^n/[n]_q! = (-(1-q)x;q)_∞`  (every `x`),

because `[n]_q! (1-q)^n = (q;q)_n`.  Their product `e_q(x) E_q(-x)` is `1`.

The `q`-derivative of a function, `D_q f(x) = (f(x) - f(qx))/((1-q)x)`, obeys
the product rule `D_q(fg)(x) = f(x) D_qg(x) + g(qx) D_qf(x)` with no
hypothesis at all, and the `q`-exponentials are its eigenfunctions:
`D_q e_q(λx) = λ e_q(λx)` and `D_q E_q(λx) = λ E_q(qλx)`.  Both follow in one
line from the tail identity `(a;q)_∞ = (1-a)(aq;q)_∞`, without touching the
series.

## Main declarations

* `qFactorial_mul_one_sub_pow`: `[n]_q! (1-q)^n = (q;q)_n`.
* `qDeriv`, `qDeriv_mul`: the `q`-derivative of functions and its product rule.
* `qExp`, `qExpBig`, `hasSum_qExp`, `hasSum_qExpBig`, `qExp_mul_qExpBig_neg`.
* `qDeriv_qExp`, `qDeriv_qExpBig`: the eigenfunction equations.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

section Factorial

variable {R : Type*} [CommRing R]

/-- `[n]_q! (1-q)^n = (q;q)_n`. -/
theorem qFactorial_mul_one_sub_pow (q : R) (n : ℕ) :
    qFactorial q n * (1 - q) ^ n = finiteQPochhammerIn q q n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [qFactorial_succ, pow_succ, finiteQPochhammerIn_succ, ← ih, ← pow_succ',
        ← one_sub_mul_qInt]
      ring

end Factorial

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

omit [CompleteSpace 𝕜] in
/-- `[n]_q! ≠ 0` for `‖q‖ < 1`. -/
theorem qFactorial_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) (n : ℕ) : qFactorial q n ≠ 0 :=
  left_ne_zero_of_mul (by rw [qFactorial_mul_one_sub_pow]; exact finiteQPochhammerIn_self_ne_zero hq n)

/-- The `q`-derivative of a function: `D_q f(x) = (f(x) - f(qx)) / ((1-q)x)`. -/
noncomputable def qDeriv (q : 𝕜) (f : 𝕜 → 𝕜) (x : 𝕜) : 𝕜 :=
  (f x - f (q * x)) / ((1 - q) * x)

omit [CompleteSpace 𝕜] in
/-- **The product rule** `D_q(fg)(x) = f(x) D_qg(x) + g(qx) D_qf(x)`, with no hypothesis. -/
theorem qDeriv_mul (q : 𝕜) (f g : 𝕜 → 𝕜) (x : 𝕜) :
    qDeriv q (fun y => f y * g y) x = f x * qDeriv q g x + g (q * x) * qDeriv q f x := by
  unfold qDeriv
  rw [mul_div_assoc', mul_div_assoc', ← add_div]
  congr 1
  ring

/-- The `q`-exponential `e_q(x) = 1/((1-q)x;q)_∞`. -/
noncomputable def qExp (q x : 𝕜) : 𝕜 := (qPochhammerInfIn ((1 - q) * x) q)⁻¹

/-- The `q`-exponential `E_q(x) = (-(1-q)x;q)_∞`. -/
noncomputable def qExpBig (q x : 𝕜) : 𝕜 := qPochhammerInfIn (-((1 - q) * x)) q

/-- **The series for `e_q`**: `∑ x^n/[n]_q! = e_q(x)` for `‖(1-q)x‖ < 1`. -/
theorem hasSum_qExp {q : 𝕜} (hq : ‖q‖ < 1) {x : 𝕜} (hx : ‖(1 - q) * x‖ < 1) :
    HasSum (fun n : ℕ => x ^ n / qFactorial q n) (qExp q x) := by
  have h1q : (1 - q) ≠ 0 := one_sub_ne_zero_of_norm_lt_one hq
  refine (hasSum_euler_reciprocal hq hx).congr_fun fun n => ?_
  rw [mul_pow, ← qFactorial_mul_one_sub_pow, mul_comm ((1 - q) ^ n),
    mul_div_mul_right _ _ (pow_ne_zero n h1q)]

/-- **The series for `E_q`**: `∑ q^{\binom n2} x^n/[n]_q! = E_q(x)` for every `x`. -/
theorem hasSum_qExpBig {q : 𝕜} (hq : ‖q‖ < 1) (x : 𝕜) :
    HasSum (fun n : ℕ => q ^ n.choose 2 * x ^ n / qFactorial q n) (qExpBig q x) := by
  have h1q : (1 - q) ≠ 0 := one_sub_ne_zero_of_norm_lt_one hq
  refine (hasSum_euler_product hq (-((1 - q) * x))).congr_fun fun n => ?_
  have h1 : ((-1 : 𝕜) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have h2 : (1 - q) ^ n ≠ 0 := pow_ne_zero n h1q
  rw [neg_pow ((1 - q) * x), mul_pow, ← qFactorial_mul_one_sub_pow]
  calc q ^ n.choose 2 * x ^ n / qFactorial q n
      = ((-1) ^ n * (-1) ^ n) * (q ^ n.choose 2 * x ^ n) * ((1 - q) ^ n / (1 - q) ^ n) /
          qFactorial q n := by rw [h1, div_self h2, one_mul, mul_one]
    _ = (-1) ^ n * q ^ n.choose 2 / (qFactorial q n * (1 - q) ^ n) *
          ((-1) ^ n * ((1 - q) ^ n * x ^ n)) := by ring

/-- `e_q(x) E_q(-x) = 1` for `‖(1-q)x‖ < 1`. -/
theorem qExp_mul_qExpBig_neg {q : 𝕜} (hq : ‖q‖ < 1) {x : 𝕜} (hx : ‖(1 - q) * x‖ < 1) :
    qExp q x * qExpBig q (-x) = 1 := by
  rw [qExp, qExpBig, mul_neg, neg_neg]
  exact inv_mul_cancel₀ (qPochhammerInfIn_ne_zero_of_norm_lt_one hq hx)

/-- **`e_q` is an eigenfunction of `D_q`**: `D_q e_q(λ·)(x) = λ e_q(λx)` for `x ≠ 0`,
within the convergence domain `‖(1-q)λx‖ < 1`. -/
theorem qDeriv_qExp {q : 𝕜} (hq : ‖q‖ < 1) (l : 𝕜) {x : 𝕜} (hx : x ≠ 0)
    (hlx : ‖(1 - q) * (l * x)‖ < 1) :
    qDeriv q (fun y => qExp q (l * y)) x = l * qExp q (l * x) := by
  have h1q : (1 - q) ≠ 0 := one_sub_ne_zero_of_norm_lt_one hq
  have hP : qPochhammerInfIn ((1 - q) * (l * x)) q ≠ 0 :=
    qPochhammerInfIn_ne_zero_of_norm_lt_one hq hlx
  have h1a : 1 - (1 - q) * (l * x) ≠ 0 := one_sub_ne_zero_of_norm_lt_one hlx
  have hPq : qPochhammerInfIn ((1 - q) * (l * x) * q) q =
      qPochhammerInfIn ((1 - q) * (l * x)) q / (1 - (1 - q) * (l * x)) := by
    rw [qPochhammerInfIn_succ_shift ((1 - q) * (l * x)) hq, mul_div_cancel_left₀ _ h1a]
  unfold qDeriv qExp
  dsimp only
  rw [show (1 - q) * (l * (q * x)) = (1 - q) * (l * x) * q by ring, hPq, inv_div,
    div_eq_iff (mul_ne_zero h1q hx)]
  ring

/-- **`E_q` is an eigenfunction of `D_q`**: `D_q E_q(λ·)(x) = λ E_q(qλx)` for `x ≠ 0`. -/
theorem qDeriv_qExpBig {q : 𝕜} (hq : ‖q‖ < 1) (l : 𝕜) {x : 𝕜} (hx : x ≠ 0) :
    qDeriv q (fun y => qExpBig q (l * y)) x = l * qExpBig q (q * (l * x)) := by
  have h1q : (1 - q) ≠ 0 := one_sub_ne_zero_of_norm_lt_one hq
  have hP : qPochhammerInfIn (-((1 - q) * (l * x))) q =
      (1 - -((1 - q) * (l * x))) * qPochhammerInfIn (-((1 - q) * (l * x)) * q) q :=
    qPochhammerInfIn_succ_shift _ hq
  unfold qDeriv qExpBig
  dsimp only
  rw [show -((1 - q) * (l * (q * x))) = -((1 - q) * (l * x)) * q by ring,
    show -((1 - q) * (q * (l * x))) = -((1 - q) * (l * x)) * q by ring, hP,
    div_eq_iff (mul_ne_zero h1q hx)]
  ring

end Fabius
