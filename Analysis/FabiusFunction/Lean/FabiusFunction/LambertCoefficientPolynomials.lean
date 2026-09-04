import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The canonical zero-based Lambert coefficient polynomials

The transseries volume's `plt:def:lambert-polynomials` and the first two
clauses of `plt:thm:lambert-recurrence`.  The large-argument expansion of
the principal Lambert branch reads `W = L₁ + ∑ₙ Pₙ(L₂) L₁⁻ⁿ` with
`L₁ = log z`, `L₂ = log log z`, and the volume takes as *definition* of
the coefficient polynomials the operator formula

`Pₙ(u) = ((-1)^{n+1}/(n+1)!) · [∏_{j<n} (∂ᵤ - j)] u^{n+1}`,

the product being empty at `n = 0`.  Two facts are proved about that
formula, both purely algebraic:

* **the boundary value** `Pₙ(0) = 0` for every `n` — each factor of the
  operator either differentiates or rescales, so the result of `n`
  factors on `u^{n+1}` vanishes to order at least `1`; and
* **the differential recurrence** `Pₙ₊₁' = n·Pₙ - Pₙ'`, i.e.
  `Pₙ₊₁' = -(∂ᵤ - n) Pₙ` — the operator commutes with `∂ᵤ`, and
  `∂ᵤ u^{n+2} = (n+2) u^{n+1}` absorbs the change of normalizing
  constant, which is exactly `-1`.

Everything is done over `ℚ`; the volume regards `Pₙ ∈ 𝕂[u]` for any
characteristic-zero `𝕂`, which is the image under `map`.

* `lambertShiftOp`, `lambertFallingOp` — `∂ᵤ - j` and `∏_{i<n}(∂ᵤ - i)`,
  with their linearity and their commutation with `∂ᵤ`.
* `lambertPoly` — `Pₙ`.
* `coeff_eq_zero_lambertShift`, `coeff_eq_zero_lambertFalling` — the
  order-of-vanishing bookkeeping.
* `lambertPoly_eval_zero` — **the boundary value** (`plt:eq:lambert-boundary`).
* `derivative_lambertPoly_succ` — **the differential recurrence**
  (`plt:eq:lambert-diff-rec`).
* `lambertPoly_zero`, `lambertPoly_one` — `P₀ = -u`, `P₁ = u`.

Not formalized here: the integral form `plt:eq:lambert-int-rec` and the
uniqueness clause, which need polynomial antidifferentiation.
-/

set_option autoImplicit false

open Polynomial

namespace Fabius

/-- The shifted derivative `∂_u - j`. -/
noncomputable def lambertShiftOp (j : ℕ) (p : ℚ[X]) : ℚ[X] :=
  derivative p - (j : ℚ) • p

/-- The falling-factorial operator `∏_{i<n} (∂_u - i)`. -/
noncomputable def lambertFallingOp : ℕ → ℚ[X] → ℚ[X]
  | 0, p => p
  | (n + 1), p => lambertShiftOp n (lambertFallingOp n p)

/-- The canonical zero-based Lambert coefficient polynomials. -/
noncomputable def lambertPoly (n : ℕ) : ℚ[X] :=
  C (((-1 : ℚ)) ^ (n + 1) / ((n + 1).factorial : ℚ)) *
    lambertFallingOp n (X ^ (n + 1))

/-- The empty product acts as the identity. -/
@[simp] theorem lambertFalling_zero (p : ℚ[X]) : lambertFallingOp 0 p = p := rfl

/-- One more factor, applied last. -/
theorem lambertFalling_succ (n : ℕ) (p : ℚ[X]) :
    lambertFallingOp (n + 1) p = lambertShiftOp n (lambertFallingOp n p) := rfl

/-- `∂ᵤ - j` is `ℚ`-linear. -/
theorem lambertShift_C_mul (j : ℕ) (c : ℚ) (p : ℚ[X]) :
    lambertShiftOp j (C c * p) = C c * lambertShiftOp j p := by
  rw [lambertShiftOp, lambertShiftOp, derivative_C_mul, mul_sub, mul_smul_comm]

/-- The falling operator is `ℚ`-linear. -/
theorem lambertFalling_C_mul (n : ℕ) (c : ℚ) (p : ℚ[X]) :
    lambertFallingOp n (C c * p) = C c * lambertFallingOp n p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lambertFalling_succ, ih, lambertShift_C_mul,
      lambertFalling_succ]

/-- `∂ᵤ - j` commutes with `∂ᵤ`. -/
theorem derivative_lambertShift (j : ℕ) (p : ℚ[X]) :
    derivative (lambertShiftOp j p) = lambertShiftOp j (derivative p) := by
  rw [lambertShiftOp, lambertShiftOp, map_sub, derivative_smul]

/-- The falling operator commutes with `∂ᵤ`, all its factors being
polynomials in `∂ᵤ`. -/
theorem derivative_lambertFalling (n : ℕ) (p : ℚ[X]) :
    derivative (lambertFallingOp n p) = lambertFallingOp n (derivative p) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lambertFalling_succ, derivative_lambertShift, ih,
      lambertFalling_succ]

/-- One shift costs at most one order of vanishing at the origin. -/
theorem coeff_eq_zero_lambertShift {m : ℕ} {p : ℚ[X]}
    (h : ∀ i < m + 1, p.coeff i = 0) (j : ℕ) :
    ∀ i < m, (lambertShiftOp j p).coeff i = 0 := by
  intro i hi
  rw [lambertShiftOp, coeff_sub, coeff_derivative, coeff_smul, smul_eq_mul,
    h (i + 1) (by omega), h i (by omega)]
  ring

/-- `∏_{i<k}(∂ - i)` applied to `u^{n+1}` still vanishes to order `n + 1 - k`. -/
theorem coeff_eq_zero_lambertFalling (n : ℕ) :
    ∀ k ≤ n, ∀ i < n + 1 - k,
      (lambertFallingOp k ((X : ℚ[X]) ^ (n + 1))).coeff i = 0 := by
  intro k
  induction k with
  | zero =>
      intro _ i hi
      rw [lambertFalling_zero, coeff_X_pow]
      exact if_neg (by omega)
  | succ k ih =>
      intro hk i hi
      have hk' : k ≤ n := by omega
      have hprev := ih hk'
      have hrewrite : n + 1 - k = (n - k) + 1 := by omega
      rw [hrewrite] at hprev
      have := coeff_eq_zero_lambertShift hprev k i (by omega)
      rwa [lambertFalling_succ]

/-- **The boundary value** (`plt:eq:lambert-boundary`): `P_n(0) = 0`. -/
theorem lambertPoly_eval_zero (n : ℕ) : (lambertPoly n).eval 0 = 0 := by
  have h := coeff_eq_zero_lambertFalling n n le_rfl 0 (by omega)
  rw [lambertPoly, eval_mul, eval_C, ← coeff_zero_eq_eval_zero, h, mul_zero]

/-- `P₀(u) = -u`. -/
theorem lambertPoly_zero : lambertPoly 0 = -X := by
  rw [lambertPoly]
  norm_num [Nat.factorial]

/-- `P₁(u) = u`. -/
theorem lambertPoly_one : lambertPoly 1 = X := by
  rw [lambertPoly, lambertFalling_succ, lambertFalling_zero, lambertShiftOp]
  simp [Nat.factorial]
  have h2 : ((1 : ℚ[X]) + 1) = C 2 := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num, C_add, C_1]
  rw [h2, ← mul_assoc, ← C_mul]
  norm_num

/-- **The differential recurrence** (`plt:eq:lambert-diff-rec`):
`P_{n+1}' = n·P_n - P_n'`, i.e. `P_{n+1}' = -(∂ - n) P_n`. -/
theorem derivative_lambertPoly_succ (n : ℕ) :
    derivative (lambertPoly (n + 1)) =
      (n : ℚ) • lambertPoly n - derivative (lambertPoly n) := by
  set c₀ : ℚ := ((-1 : ℚ)) ^ (n + 1) / ((n + 1).factorial : ℚ) with hc₀
  set c₁ : ℚ := ((-1 : ℚ)) ^ (n + 1 + 1) / ((n + 1 + 1).factorial : ℚ) with hc₁
  have hc₀ne : c₀ ≠ 0 := by
    rw [hc₀]
    exact div_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast (n + 1).factorial_ne_zero)
  have hconst : c₁ * ((n + 1 + 1 : ℕ) : ℚ) * c₀⁻¹ = -1 := by
    rw [hc₀, hc₁, Nat.factorial_succ (n + 1)]
    have h1 : (((n + 1).factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (n + 1).factorial_ne_zero
    push_cast
    field_simp
    ring
  have hF : lambertFallingOp n (X ^ (n + 1)) = C c₀⁻¹ * lambertPoly n := by
    rw [lambertPoly, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc₀ne, C_1, one_mul]
  rw [lambertPoly, derivative_C_mul, derivative_lambertFalling, derivative_X_pow,
    Nat.add_sub_cancel, lambertFalling_C_mul, lambertFalling_succ, hF,
    lambertShift_C_mul]
  simp only [← mul_assoc, ← C_mul]
  rw [hconst, lambertShiftOp, C_neg, C_1, neg_one_mul, neg_sub]

end Fabius
