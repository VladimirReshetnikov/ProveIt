import FabiusFunction.CompleteHomogeneousBell
import FabiusFunction.LambertPhaseLockedRichardson

/-!
# Bell forms of phase-locked reciprocal-grid moments

The exact higher moments of the phase-locked reciprocal Lagrange row are
already expressed in `LambertPhaseLockedRichardson` through complete
homogeneous evaluations at the shifted reciprocal alphabet

`(lambda + j)⁻¹`, `0 ≤ j ≤ r`.

This module applies the generic complete-homogeneous--Bell identity to that
finite alphabet.  Its power sums are the generalized harmonic sums

`H_k^(r)(lambda) = ∑ j ≤ r, (lambda + j)⁻ᵏ`,

and the Bell input at positive index `k + 1` is
`k! * H_(k+1)^(r)(lambda)`.  The two final theorems are respectively the
offset form with exponent `r + 1 + n` and the report-shaped form with
exponent `r + s`, `s ≥ 1`.

Everything here is finite algebra.  Inversion in a field is total, so the
identities require no positivity or nonvanishing hypothesis on `lambda`.

## Main results

* `shiftedReciprocalPowerSum` is the generalized harmonic power sum.
* `shiftedReciprocalBellInput` is its factorially weighted Bell input.
* `completeHomogeneousEvalOn_shiftedReciprocal_eq_bell` specializes the
  generic complete-homogeneous--Bell identity.
* `sum_shiftedReciprocalLagrangeWeight_mul_invPow_card_add_eq_bell` is the
  all-offset exact reciprocal moment in Bell form.
* `sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_bell` is its
  report-shaped `s ≥ 1` form.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

/-- The generalized power sum of the shifted reciprocal alphabet
`(lambda + j)⁻¹`, `0 ≤ j ≤ r`. -/
def shiftedReciprocalPowerSum
    {K : Type*} [Field K] (lambda : K) (r k : ℕ) : K :=
  completeHomogeneousPowerSum (Finset.range (r + 1))
    (shiftedReciprocalNode lambda) k

/-- The complete-Bell input attached to the shifted reciprocal alphabet.
Its zeroth value is zero, and its value at `k + 1` is
`k! * shiftedReciprocalPowerSum lambda r (k + 1)`. -/
def shiftedReciprocalBellInput
    {K : Type*} [Field K] (lambda : K) (r : ℕ) : ℕ → K :=
  completeHomogeneousBellInput (Finset.range (r + 1))
    (shiftedReciprocalNode lambda)

/-- The shifted reciprocal power sum in its displayed finite-sum form. -/
theorem shiftedReciprocalPowerSum_eq_sum
    {K : Type*} [Field K] (lambda : K) (r k : ℕ) :
    shiftedReciprocalPowerSum lambda r k =
      ∑ j ∈ Finset.range (r + 1), (lambda + (j : K))⁻¹ ^ k := by
  rfl

/-- The normalized zeroth Bell input is zero. -/
@[simp]
theorem shiftedReciprocalBellInput_zero
    {K : Type*} [Field K] (lambda : K) (r : ℕ) :
    shiftedReciprocalBellInput lambda r 0 = 0 := by
  rfl

/-- At every positive index, the Bell input is the factorially weighted
generalized harmonic power sum. -/
@[simp]
theorem shiftedReciprocalBellInput_succ
    {K : Type*} [Field K] (lambda : K) (r k : ℕ) :
    shiftedReciprocalBellInput lambda r (k + 1) =
      (k.factorial : K) * shiftedReciprocalPowerSum lambda r (k + 1) := by
  rfl

/-- Complete homogeneous evaluation on the shifted reciprocal alphabet is
the factorially normalized complete Bell polynomial of its generalized
harmonic power sums. -/
theorem completeHomogeneousEvalOn_shiftedReciprocal_eq_bell
    {K : Type*} [Field K] [Algebra ℚ K]
    (lambda : K) (r n : ℕ) :
    completeHomogeneousEvalOn (Finset.range (r + 1))
        (fun j ↦ (lambda + (j : K))⁻¹) n =
      factorialNormalize
        (completeBellPolynomial (shiftedReciprocalBellInput lambda r)) n := by
  change completeHomogeneousEvalOn (Finset.range (r + 1))
      (shiftedReciprocalNode lambda) n =
    factorialNormalize
      (completeBellPolynomial
        (completeHomogeneousBellInput (Finset.range (r + 1))
          (shiftedReciprocalNode lambda))) n
  exact completeHomogeneousEvalOn_eq_factorialNormalize_completeBellPolynomial
    (R := K) (Finset.range (r + 1)) (shiftedReciprocalNode lambda) n

/-- The exact reciprocal-grid moment at exponent `r + 1 + n`, rewritten as
the nodal reciprocal product times a complete Bell polynomial. -/
theorem
    sum_shiftedReciprocalLagrangeWeight_mul_invPow_card_add_eq_bell
    {K : Type*} [Field K] [CharZero K]
    (lambda : K) (r n : ℕ) :
    (∑ j ∈ Finset.range (r + 1),
      shiftedReciprocalLagrangeWeight lambda r j *
        (lambda + (j : K))⁻¹ ^ (r + 1 + n)) =
      (-1 : K) ^ r *
        (∏ j ∈ Finset.range (r + 1),
          (lambda + (j : K))⁻¹) *
        factorialNormalize
          (completeBellPolynomial (shiftedReciprocalBellInput lambda r)) n := by
  rw [sum_shiftedReciprocalLagrangeWeight_mul_invPow_card_add,
    completeHomogeneousEvalOn_shiftedReciprocal_eq_bell]

/-- Report-shaped Bell form of every residual reciprocal-grid moment.  For
`s ≥ 1`, the degree-`r + s` moment is the signed reciprocal rising-factorial
prefactor times the factorially normalized Bell polynomial of degree
`s - 1`. -/
theorem sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_bell
    {K : Type*} [Field K] [CharZero K]
    (lambda : K) (r s : ℕ) (hs : 1 ≤ s) :
    (∑ j ∈ Finset.range (r + 1),
      shiftedReciprocalLagrangeWeight lambda r j *
        (lambda + (j : K))⁻¹ ^ (r + s)) =
      (-1 : K) ^ r /
          (∏ j ∈ Finset.range (r + 1), (lambda + (j : K))) *
        factorialNormalize
          (completeBellPolynomial (shiftedReciprocalBellInput lambda r))
            (s - 1) := by
  rw [sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_completeHomogeneous
      lambda r s hs,
    completeHomogeneousEvalOn_shiftedReciprocal_eq_bell]

end

end Fabius
