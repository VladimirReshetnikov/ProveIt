import FabiusFunction.LambertCoefficientPolynomials
import FabiusFunction.StirlingBasisChange
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The Stirling-number formula for the Lambert coefficient polynomials

The transseries volume's `plt:thm:lambert-stirling`, in its coefficient
form `plt:eq:lambert-lambda`: for `m ≤ n + 1`,

`[u^m] Pₙ = ((-1)^{n+1} / m!) · s(n, n+1-m)`,

with `s` the signed Stirling numbers of the first kind of
`StirlingBasisChange`.  In particular `Pₙ` has degree `n` with leading
coefficient `1/n`, and its coefficients alternate in sign
(`plt:cor:lambert-coefficients`, read off from this formula and the
positivity of the unsigned numbers).

The route is the one the volume takes, made literal: the falling
operator `∏_{j<n}(∂ᵤ - j)` *is* the falling factorial `u(u-1)⋯(u-n+1)`
evaluated at the commuting operator `∂ᵤ`.  That evaluation is
`Polynomial.aeval` into the endomorphism algebra of `ℚ[u]` (`derivEval`),
which is multiplicative for free; the corpus's expansion
`descPochhammer_eq_sum_monomial_signedStirlingFirst` then turns the
operator into `∑ₖ s(n,k) ∂ᵤᵏ`, and `∂ᵤᵏ u^{n+1}` is the falling power
`(n+1)(n)⋯(n+2-k) · u^{n+1-k}`, which reads off the coefficient.

* `derivEval` — `q ↦ q(∂ᵤ)`, with `derivEval_mul`, `derivEval_X_sub_natCast`.
* `lambertFallingOp_eq_derivEval` — **the operator is the falling
  factorial at `∂ᵤ`**.
* `derivEval_descPochhammer_apply` — the Stirling expansion of the operator.
* `coeff_lambertPoly` — **the coefficient formula**.
-/

set_option autoImplicit false

open Polynomial Finset

namespace Fabius

/-- Evaluation of a polynomial at the derivation `∂_u`, as an endomorphism
of `ℚ[u]`: `q(∂_u)`. -/
noncomputable def derivEval (q : ℚ[X]) : Module.End ℚ ℚ[X] :=
  aeval (derivative : ℚ[X] →ₗ[ℚ] ℚ[X]) q

/-- `(qr)(∂ᵤ) = q(∂ᵤ) r(∂ᵤ)`: evaluation at a commuting operator is multiplicative. -/
theorem derivEval_mul (q r : ℚ[X]) :
    derivEval (q * r) = derivEval q * derivEval r := by
  rw [derivEval, derivEval, derivEval, map_mul]

/-- `(u - j)(∂ᵤ)` is the shifted derivative `∂ᵤ - j`. -/
theorem derivEval_X_sub_natCast (n : ℕ) (p : ℚ[X]) :
    derivEval (X - (n : ℚ[X])) p = lambertShiftOp n p := by
  rw [derivEval, map_sub, aeval_X, map_natCast, LinearMap.sub_apply,
    Module.End.natCast_apply, lambertShiftOp, Nat.cast_smul_eq_nsmul]

/-- **The falling operator is the falling factorial evaluated at `∂_u`.** -/
theorem lambertFallingOp_eq_derivEval (n : ℕ) (p : ℚ[X]) :
    lambertFallingOp n p = derivEval (descPochhammer ℚ n) p := by
  induction n with
  | zero => simp [derivEval, descPochhammer_zero]
  | succ n ih =>
      rw [lambertFalling_succ, ih, descPochhammer_succ_right, mul_comm,
        derivEval_mul, Module.End.mul_apply, derivEval_X_sub_natCast]

/-- The falling factorial at `∂_u`, expanded through the signed Stirling
numbers of the first kind. -/
theorem derivEval_descPochhammer_apply (n : ℕ) (p : ℚ[X]) :
    derivEval (descPochhammer ℚ n) p =
      ∑ k ∈ range (n + 1),
        (signedStirlingFirst n k : ℚ) • (⇑derivative)^[k] p := by
  rw [derivEval, descPochhammer_eq_sum_monomial_signedStirlingFirst, map_sum,
    LinearMap.sum_apply]
  refine sum_congr rfl fun k _ => ?_
  rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
    Module.End.pow_apply]

/-- **The Stirling-number formula** (`plt:eq:lambert-lambda`, signed form):
for `m ≤ n + 1`,
`[u^m] P_n = ((-1)^{n+1}/m!) · s(n, n+1-m)`. -/
theorem coeff_lambertPoly (n m : ℕ) (hm : m ≤ n + 1) :
    (lambertPoly n).coeff m =
      (-1) ^ (n + 1) / (m.factorial : ℚ) *
        (signedStirlingFirst n (n + 1 - m) : ℚ) := by
  rw [lambertPoly, lambertFallingOp_eq_derivEval, derivEval_descPochhammer_apply,
    coeff_C_mul, finsetSum_coeff]
  simp only [iterate_derivative_X_pow_eq_smul, coeff_smul, coeff_X_pow, smul_eq_mul]
  rw [sum_eq_single (n + 1 - m)]
  · rw [if_pos (by omega)]
    have hfac : ((n + 1 - (n + 1 - m)).factorial : ℚ) *
        (((n + 1).descFactorial (n + 1 - m) : ℕ) : ℚ) = ((n + 1).factorial : ℚ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial (by omega : n + 1 - m ≤ n + 1)
    rw [show n + 1 - (n + 1 - m) = m by omega] at hfac
    have hm0 : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hn0 : ((n + 1).factorial : ℚ) ≠ 0 := by
      exact_mod_cast (n + 1).factorial_ne_zero
    field_simp
    rw [← hfac]
    ring
  · intro k hk hne
    rw [mem_range] at hk
    rw [if_neg (by omega), mul_zero, mul_zero]
  · intro hnot
    rw [mem_range, not_lt] at hnot
    have : m = 0 := by omega
    subst this
    rw [signedStirlingFirst_eq_zero_of_lt (by omega)]
    simp

end Fabius
