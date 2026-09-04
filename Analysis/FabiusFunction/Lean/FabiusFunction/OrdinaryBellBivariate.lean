import FabiusFunction.OrdinaryBellComposition
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# The bivariate generating function of the ordinary Bell polynomials

This closes the one identity of the source's Bell-polynomial generating-function theorem that
the corpus did not carry:

`exp(u X̂(t)) = ∑_{n ≥ k ≥ 0} B̂_{n,k}(x) t^n u^k / k!`   (`coeff_exp_subst_smul`),

read on the coefficient of `t^n`.  The exponential companion `exp(u X(t))` was already
`exp_subst_smul_bellWeightSeries`, and the ordinary univariate form `X̂(t)^k` was already
`coeff_pow_eq_ordPartialBell`.

The statement is made for an arbitrary series `f` with no constant term rather than for the
source's `X̂(t) = ∑_{j ≥ 1} x_j t^j`; the source's form is the case `coeff i f = x_i`.  The
scalar `u` ranges over the algebra, so `u` is a parameter and not a second formal variable,
which is what the corpus's exponential bivariate statement also does.

The proof is the ordinary composition theorem `coeff_subst_eq_sum_ordPartialBell` together
with the homogeneity `ordPartialBell_mul_left`, which is what turns the scaled weights
`u x_i` into the factor `u^k`.

## Main results

* `constantCoeff_smul_eq_zero`, `coeff_smul_eq_mul`.
* `coeff_exp_subst_smul`, the bivariate identity.
* `coeff_exp_subst`, its value at `u = 1`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section Bivariate

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Scaling a series without constant term leaves it without constant term. -/
theorem constantCoeff_smul_eq_zero (u : A) {f : A⟦X⟧} (hf : constantCoeff f = 0) :
    constantCoeff (u • f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_smul, smul_eq_mul, coeff_zero_eq_constantCoeff, hf,
    mul_zero]

/-- The coefficients of a scaled series are the scaled coefficients. -/
theorem coeff_smul_eq_mul (u : A) (f : A⟦X⟧) :
    (fun i => coeff i (u • f)) = fun i => u * coeff i f := by
  funext i
  rw [coeff_smul, smul_eq_mul]

/-- **The bivariate generating function of the ordinary Bell polynomials:**
`[t^n] exp(u X̂(t)) = ∑_{k ≤ n} B̂_{n,k}(x) u^k / k!`. -/
theorem coeff_exp_subst_smul (u : A) {f : A⟦X⟧} (hf : constantCoeff f = 0) (n : ℕ) :
    coeff n ((exp A).subst (u • f)) =
      ∑ k ∈ range (n + 1), algebraMap ℚ A (1 / k.factorial) * u ^ k *
        ordPartialBell (fun i => coeff i f) n k := by
  rw [coeff_subst_eq_sum_ordPartialBell _ (constantCoeff_smul_eq_zero A u hf) n]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_smul_eq_mul, ordPartialBell_mul_left, coeff_exp]
  ring

/-- At `u = 1`: `[t^n] exp(X̂(t)) = ∑_{k ≤ n} B̂_{n,k}(x)/k!`. -/
theorem coeff_exp_subst {f : A⟦X⟧} (hf : constantCoeff f = 0) (n : ℕ) :
    coeff n ((exp A).subst f) =
      ∑ k ∈ range (n + 1), algebraMap ℚ A (1 / k.factorial) *
        ordPartialBell (fun i => coeff i f) n k := by
  have h := coeff_exp_subst_smul A (1 : A) hf n
  rw [one_smul] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one]

end Bivariate

end Fabius
