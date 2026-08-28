import FabiusFunction.MomentCumulantAlgebra
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Probability.Moments.Basic

/-!
# Polynomial expectations from moments and cumulants

The expectation of a finite polynomial is determined by finitely many raw
moments.  This module records that elementary fact with economical local
hypotheses, then combines it with the all-orders moment--cumulant inversion in
`MomentCumulantAlgebra`.

For a polynomial `p`, the theorem assumes integrability only at indices in
`p.support`.  Its coefficient semiring may be unrelated to `ℝ`, provided a
ring homomorphism maps the coefficients into `ℝ`.  The first three results
use no boundedness, independence, convergence of an infinite series, or
probability normalization of the chosen measure.

The cumulant theorem is the reusable finite moment-to-Bell rewrite used by
the endpoint-transfer sentence in the frontier reports: after taking `p` to
be a universal endpoint-transfer polynomial, its tilted integral is a finite
coefficient-weighted complete Bell transform of the formal cumulants of the
tilted raw moments.  The transfer expansion itself, analytic Taylor
remainders, and tail estimates remain separate.

## Main results

* `integral_eval₂_eq_sum_moment` expands the integral of any finite
  polynomial into its coefficient-weighted raw moments.
* `integral_eval₂_eq_sum_completeBell_momentCumulant_with_mass_correction`
  replaces those raw moments by the complete Bell transform of their formal
  cumulants, with the exact correction for an arbitrary zeroth moment.
* `integral_eval₂_eq_sum_completeBell_momentCumulant` is the canonical
  probability-measure specialization.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace Fabius

noncomputable section

/-- **Finite polynomial integral from raw moments.**  If the powers
indexed by `p.support` are integrable, then the integral of `p(Z)` is the
finite sum of each mapped coefficient times the corresponding raw moment.

The polynomial coefficients may lie in any semiring admitting a ring
homomorphism to `ℝ`; no probability normalization of the measure is needed. -/
theorem integral_eval₂_eq_sum_moment
    {Ω A : Type*} [MeasurableSpace Ω] [Semiring A]
    (μ : Measure Ω) (Z : Ω → ℝ) (φ : A →+* ℝ)
    (p : Polynomial A)
    (hZ : ∀ n ∈ p.support, Integrable (fun ω ↦ Z ω ^ n) μ) :
    (∫ ω, p.eval₂ φ (Z ω) ∂μ) =
      p.sum (fun n a ↦ φ a * ProbabilityTheory.moment Z n μ) := by
  rw [show (fun ω ↦ p.eval₂ φ (Z ω)) =
      fun ω ↦ ∑ n ∈ p.support, φ (p.coeff n) * Z ω ^ n by
        funext ω
        rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]]
  rw [integral_finsetSum p.support
    (fun n hn ↦ (hZ n hn).const_mul (φ (p.coeff n)))]
  rw [Polynomial.sum_def]
  refine Finset.sum_congr rfl fun n _hn ↦ ?_
  rw [integral_const_mul]
  rfl

/-- **Finite polynomial integral from formal cumulants, with arbitrary
zeroth moment.**  The integral of any finite polynomial is its
coefficient-weighted complete Bell transform, plus the exact constant-term correction

`mapped constant coefficient * (zeroth moment - 1)`.

This is the normalization-free form of the integral--cumulant identity.  The
correction is unavoidable because the formal complete Bell transform installs
zeroth moment one, independently of the supplied moment sequence. -/
theorem integral_eval₂_eq_sum_completeBell_momentCumulant_with_mass_correction
    {Ω A : Type*} [MeasurableSpace Ω] [Semiring A]
    (μ : Measure Ω) (Z : Ω → ℝ) (φ : A →+* ℝ)
    (p : Polynomial A)
    (hZ : ∀ n ∈ p.support, Integrable (fun ω ↦ Z ω ^ n) μ) :
    (∫ ω, p.eval₂ φ (Z ω) ∂μ) =
      p.sum (fun n a ↦
        φ a * completeBellPolynomial
          (momentCumulant
            (fun k ↦ ProbabilityTheory.moment Z k μ)) n) +
        φ (p.coeff 0) * (ProbabilityTheory.moment Z 0 μ - 1) := by
  let m : ℕ → ℝ := fun k ↦ ProbabilityTheory.moment Z k μ
  rw [integral_eval₂_eq_sum_moment μ Z φ p hZ]
  rw [Polynomial.sum_def, Polynomial.sum_def]
  calc
    ∑ n ∈ p.support, φ (p.coeff n) * m n =
        ∑ n ∈ p.support,
          (φ (p.coeff n) * completeBellPolynomial (momentCumulant m) n +
            if n = 0 then φ (p.coeff n) * (m 0 - 1) else 0) := by
      refine Finset.sum_congr rfl fun n _hn ↦ ?_
      rw [completeBellPolynomial_momentCumulant]
      by_cases hn : n = 0
      · subst n
        simp
        ring
      · simp [hn]
    _ = (∑ n ∈ p.support,
          φ (p.coeff n) * completeBellPolynomial (momentCumulant m) n) +
        ∑ n ∈ p.support,
          if n = 0 then φ (p.coeff n) * (m 0 - 1) else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ n ∈ p.support,
          φ (p.coeff n) * completeBellPolynomial (momentCumulant m) n) +
        φ (p.coeff 0) * (m 0 - 1) := by
      congr 1
      by_cases hzero : p.coeff 0 = 0 <;>
        simp [Polynomial.mem_support_iff, hzero]

/-- **Normalized finite polynomial integral from formal cumulants.**  If
the zeroth raw moment of `Z` is one, then the constant correction vanishes
and the polynomial integral is exactly the coefficient-weighted complete Bell
transform of the formal cumulants of its raw-moment sequence.

The theorem assumes integrability only for powers indexed by the support of
`p`; in particular, it does not require an all-moments hypothesis. -/
theorem integral_eval₂_eq_sum_completeBell_momentCumulant_of_moment_zero_eq_one
    {Ω A : Type*} [MeasurableSpace Ω] [Semiring A]
    (μ : Measure Ω) (Z : Ω → ℝ) (φ : A →+* ℝ)
    (p : Polynomial A)
    (hZ : ∀ n ∈ p.support, Integrable (fun ω ↦ Z ω ^ n) μ)
    (hzero : ProbabilityTheory.moment Z 0 μ = 1) :
    (∫ ω, p.eval₂ φ (Z ω) ∂μ) =
      p.sum (fun n a ↦
        φ a * completeBellPolynomial
          (momentCumulant
            (fun k ↦ ProbabilityTheory.moment Z k μ)) n) := by
  rw [integral_eval₂_eq_sum_completeBell_momentCumulant_with_mass_correction
    μ Z φ p hZ, hzero, sub_self, mul_zero, add_zero]

/-- **Polynomial expectation under a probability measure.**  For a
probability law, the expectation of any finite polynomial is exactly the
coefficient-weighted complete Bell transform of the formal cumulants of its
raw moments.  Only powers in the polynomial support must be integrable. -/
theorem integral_eval₂_eq_sum_completeBell_momentCumulant
    {Ω A : Type*} [MeasurableSpace Ω] [Semiring A]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (φ : A →+* ℝ)
    (p : Polynomial A)
    (hZ : ∀ n ∈ p.support, Integrable (fun ω ↦ Z ω ^ n) μ) :
    (∫ ω, p.eval₂ φ (Z ω) ∂μ) =
      p.sum (fun n a ↦
        φ a * completeBellPolynomial
          (momentCumulant
            (fun k ↦ ProbabilityTheory.moment Z k μ)) n) := by
  exact integral_eval₂_eq_sum_completeBell_momentCumulant_of_moment_zero_eq_one
    μ Z φ p hZ (by simp [ProbabilityTheory.moment])

end

end Fabius
