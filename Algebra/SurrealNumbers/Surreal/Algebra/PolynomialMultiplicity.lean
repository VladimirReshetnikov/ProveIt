import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Polynomial multiplicity and finite Taylor expansion

This file formalizes the multiplicity and finite Taylor clauses of
`polynomial:thm:fta` in `docs/surcomplex/polynomial-algebra/article.tex`.
The statements hold over any characteristic-zero field, without requiring
algebraic closedness. All derivatives are formal polynomial derivatives and
all sums are finite.

Mathlib's `Polynomial.rootMultiplicity` is zero for the zero polynomial. We
therefore require a nonzero polynomial when characterizing multiplicity by
the first nonvanishing derivative. The derivative formula at a root uses
natural-number subtraction, and also respects Mathlib's zero convention.
-/

namespace Surreal
namespace FinitePolynomial

open Polynomial

variable {K : Type*} [Field K]

/-- All derivatives below the root multiplicity vanish at the root. This is
the vanishing direction of `polynomial:thm:fta`'s multiplicity criterion. -/
theorem eval_iterate_derivative_eq_zero_of_lt_multiplicity (p : K[X]) (a : K)
    {j : ℕ} (hj : j < p.rootMultiplicity a) :
    (derivative^[j] p).eval a = 0 :=
  Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hj

variable [CharZero K]

/-- For a nonzero polynomial, the derivative of order exactly its root
multiplicity is nonzero at the point (`polynomial:thm:fta`). -/
theorem eval_iterate_derivative_multiplicity_ne_zero (p : K[X]) (hp : p ≠ 0)
    (a : K) : (derivative^[p.rootMultiplicity a] p).eval a ≠ 0 := by
  rw [Polynomial.eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hp)

/-- The multiplicity is precisely the first order at which the formal
derivative does not vanish (`polynomial:thm:fta`). The zero polynomial is
excluded because it has no such derivative. -/
theorem multiplicity_eq_iff_derivatives (p : K[X]) (hp : p ≠ 0) (a : K) (m : ℕ) :
    p.rootMultiplicity a = m ↔
      (∀ j < m, (derivative^[j] p).eval a = 0) ∧
        (derivative^[m] p).eval a ≠ 0 := by
  constructor
  · rintro rfl
    exact ⟨fun j hj => eval_iterate_derivative_eq_zero_of_lt_multiplicity p a hj,
      eval_iterate_derivative_multiplicity_ne_zero p hp a⟩
  · rintro ⟨hzero, hne⟩
    apply le_antisymm
    · exact le_of_not_gt fun h =>
        hne (eval_iterate_derivative_eq_zero_of_lt_multiplicity p a h)
    · exact le_of_not_gt fun h =>
        eval_iterate_derivative_multiplicity_ne_zero p hp a (hzero _ h)

/-- The least-index formulation of the multiplicity clause of
`polynomial:thm:fta`. -/
theorem multiplicity_isLeast_nonzero_derivative (p : K[X]) (hp : p ≠ 0) (a : K) :
    IsLeast {j : ℕ | (derivative^[j] p).eval a ≠ 0} (p.rootMultiplicity a) := by
  refine ⟨eval_iterate_derivative_multiplicity_ne_zero p hp a, ?_⟩
  intro j hj
  exact le_of_not_gt fun h => hj (eval_iterate_derivative_eq_zero_of_lt_multiplicity p a h)

/-- At a root, differentiation lowers multiplicity by one. This is the
local calculation in the proof of `polynomial:eq:logderivative`. -/
theorem derivative_rootMultiplicity {p : K[X]} {a : K} (ha : p.IsRoot a) :
    p.derivative.rootMultiplicity a = p.rootMultiplicity a - 1 :=
  Polynomial.derivative_rootMultiplicity_of_root ha

omit [CharZero K] in
/-- A multiple root of a nonzero polynomial is exactly a common root of
the polynomial and its derivative (`polynomial:thm:fta`). -/
theorem multiple_root_iff (p : K[X]) (hp : p ≠ 0) (a : K) :
    1 < p.rootMultiplicity a ↔ p.eval a = 0 ∧ p.derivative.eval a = 0 :=
  Polynomial.one_lt_rootMultiplicity_iff_isRoot hp

/-- The Taylor coefficient is the evaluated formal derivative divided by
its factorial. This identifies Mathlib's Hasse derivative formulation with
the characteristic-zero formula in the proof of `polynomial:thm:fta`. -/
theorem taylor_coeff_eq_derivative (p : K[X]) (a : K) (j : ℕ) :
    (taylor a p).coeff j = (derivative^[j] p).eval a / (j.factorial : K) := by
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))).mpr
  rw [taylor_coeff, ← factorial_smul_hasseDeriv]
  change (hasseDeriv j p).eval a * (j.factorial : K) =
    (j.factorial • hasseDeriv j p).eval a
  rw [eval_smul, nsmul_eq_mul, mul_comm]

/-- The finite Taylor identity `P(a + X) = ∑ P⁽ʲ⁾(a)/j! Xʲ`, used in
`polynomial:thm:fta`. No convergence assertion is involved. -/
theorem taylor_eq_sum_derivatives (p : K[X]) (a : K) :
    taylor a p = ∑ j ∈ Finset.range (p.natDegree + 1),
      C ((derivative^[j] p).eval a / (j.factorial : K)) * X ^ j := by
  simpa only [natDegree_taylor, taylor_coeff_eq_derivative] using
    (taylor a p).as_sum_range_C_mul_X_pow

/-- Expansion in powers of `X - a`, the finite Taylor form used for
Hermite jets in `polynomial:eq:finiteCRT`. -/
theorem eq_sum_derivatives (p : K[X]) (a : K) :
    p = ∑ j ∈ Finset.range (p.natDegree + 1),
      C ((derivative^[j] p).eval a / (j.factorial : K)) * (X - C a) ^ j := by
  have h := Polynomial.sum_taylor_eq p a
  rw [Polynomial.sum_over_range _ (fun j => by simp)] at h
  simpa only [natDegree_taylor, taylor_coeff_eq_derivative] using h.symm

/-- Evaluating the finite Taylor expansion at an arbitrary increment. -/
theorem eval_add_eq_sum_derivatives (p : K[X]) (a y : K) :
    p.eval (a + y) = ∑ j ∈ Finset.range (p.natDegree + 1),
      ((derivative^[j] p).eval a / (j.factorial : K)) * y ^ j := by
  have h := congrArg (Polynomial.eval y) (taylor_eq_sum_derivatives p a)
  simpa only [taylor_eval, add_comm y a, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X] using h

/-- Vanishing of a finite derivative jet is equivalent to divisibility by
the corresponding power of the linear factor. This includes the zero
polynomial, and supplies the local kernel calculation in
`polynomial:thm:crt`. -/
theorem pow_linear_dvd_iff_derivatives_vanish (p : K[X]) (a : K) (m : ℕ) :
    (X - C a) ^ m ∣ p ↔ ∀ j < m, (derivative^[j] p).eval a = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  constructor
  · intro h j hj
    exact eval_iterate_derivative_eq_zero_of_lt_multiplicity p a
      (hj.trans_le ((Polynomial.le_rootMultiplicity_iff hp).mpr h))
  · intro h
    apply (Polynomial.le_rootMultiplicity_iff hp).mp
    exact le_of_not_gt fun hm =>
      eval_iterate_derivative_multiplicity_ne_zero p hp a (h _ hm)

/-- Two polynomials have the same finite derivative jet at `a` exactly
when their difference is divisible by the local modulus. This is the
well-definedness and injectivity calculation behind
`polynomial:eq:finiteCRT`. -/
theorem derivative_jets_eq_iff_dvd_sub (p q : K[X]) (a : K) (m : ℕ) :
    (∀ j < m, (derivative^[j] p).eval a = (derivative^[j] q).eval a) ↔
      (X - C a) ^ m ∣ p - q := by
  rw [pow_linear_dvd_iff_derivatives_vanish]
  simp only [Polynomial.iterate_derivative_sub, eval_sub, sub_eq_zero]

end FinitePolynomial
end Surreal
