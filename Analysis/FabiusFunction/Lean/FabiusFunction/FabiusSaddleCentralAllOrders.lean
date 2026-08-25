import FabiusFunction.FabiusSaddleExpansionCoefficients
import FabiusFunction.SaddleExpansionFiniteRemainder
import FabiusFunction.FabiusSaddleCentralLambert
import FabiusFunction.NegativeLaplaceVerticalAllOrderBound
import FabiusFunction.FabiusSaddleExponentAllOrders
import FabiusFunction.FabiusSaddleTailAllOrders
import FabiusFunction.GaussianPolynomialTailAllOrders
import FabiusFunction.FabiusSaddleReferenceWeight

/-!
# Exact all-order central saddle decomposition

This module identifies the finite polynomial reference on the dyadic Lambert
orbit, contracts its odd terms, and decomposes the exact centered saddle
exponent into its periodic truncation and explicit analytic remainders.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace Fabius

open SaddleExpansion

noncomputable section

/-- Evaluation commutes with the formal exponential recursion: evaluating
the polynomial `expCoeff (negativeLaplaceExponentPolynomial · t) n` at
`(v : ℂ)` gives the scalar coefficient
`expCoeff (negativeLaplaceExponentCoefficient · t v) n`.  Proved by
transporting `expCoeff` along the `ℚ`-algebra map `Polynomial.aeval v`. -/
theorem negativeLaplaceExpCoeff_eval
    (n : ℕ) (t v : ℝ) :
    (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).eval (v : ℂ) =
      expCoeff (fun m => negativeLaplaceExponentCoefficient m t v) n := by
  let ev : Polynomial ℂ →ₐ[ℚ] ℂ :=
    (Polynomial.aeval (v : ℂ)).restrictScalars ℚ
  change ev (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n) = _
  rw [map_expCoeff ev]
  apply expCoeff_congr n
  intro m _hm
  exact negativeLaplaceExponentPolynomial_eval m t v

/-- Parity of the exponential coefficient polynomials: the `n`-th one
evaluates at `-v` to `(-1) ^ n` times its value at `v`.  It is inherited
from the parity of the scalar exponent coefficients through
`negativeLaplaceExpCoeff_eval`. -/
theorem negativeLaplaceExpCoeff_eval_neg
    (n : ℕ) (t v : ℝ) :
    (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).eval ((-v : ℝ) : ℂ) =
      (-1 : ℂ) ^ n *
        (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).eval (v : ℂ) := by
  rw [negativeLaplaceExpCoeff_eval, negativeLaplaceExpCoeff_eval]
  simpa only [expCoeff_apply] using
    expCoeff_parity (fun m v => negativeLaplaceExponentCoefficient m t v)
      (fun m v => negativeLaplaceExponentCoefficient_parity m t v) n v

/-- Odd-index exponential coefficients contract to zero: the Gaussian
contraction of `expCoeff (negativeLaplaceExponentPolynomial · t) (2 * j + 1)`
vanishes for every `j` and every real `t`.  The contraction is a
Gaussian-weighted integral and the integrand is odd by
`negativeLaplaceExpCoeff_eval_neg`. -/
theorem gaussianPolynomialContraction_negativeLaplaceExpCoeff_odd
    (j : ℕ) (t : ℝ) :
    gaussianPolynomialContraction
        (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) (2 * j + 1)) = 0 := by
  rw [gaussianPolynomialContraction_eq_integral]
  rw [QuantitativeSaddle.integral_eq_zero_of_odd]
  · simp
  · intro v
    simp only [QuantitativeSaddle.standardGaussian, neg_sq]
    rw [negativeLaplaceExpCoeff_eval_neg]
    rw [show (-1 : ℂ) ^ (2 * j + 1) = -1 by
      rw [pow_add, pow_mul]
      norm_num]
    ring

private lemma sum_range_two_mul_pair
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) (N : ℕ) :
    ∑ k ∈ Finset.range (2 * N), f k =
      ∑ j ∈ Finset.range N, (f (2 * j) + f (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      abel

/-- Reciprocal square-root scale on the dyadic Lambert saddle. -/
noncomputable def dyadicLambertEpsilon (t : ℝ) : ℝ :=
  (Real.sqrt (dyadicLambertPhase t))⁻¹

/-- Squaring the reciprocal square-root scale inverts the phase, under the
hypothesis `0 < dyadicLambertPhase t`.  Also used in
`FabiusSaddleMassAllOrders`. -/
lemma dyadicLambertEpsilon_sq {t : ℝ} (ht : 0 < dyadicLambertPhase t) :
    dyadicLambertEpsilon t ^ 2 = (dyadicLambertPhase t)⁻¹ := by
  unfold dyadicLambertEpsilon
  rw [inv_pow, Real.sq_sqrt ht.le]

/-- Order-`N` polynomial reference on the dyadic Lambert orbit: the saddle
reference polynomial in the Gaussian variable, truncated at epsilon-length
`2 * (N + 1)`, that is retaining the epsilon-orders `0` through `2 * N + 1`,
at phase `dyadicLambertPhase t` and scale `dyadicLambertEpsilon t`.  The
even orders are the `N + 1` ones that survive the Gaussian contraction; the
odd ones are carried along and cancel there. -/
noncomputable def dyadicLambertReferencePolynomial
    (N : ℕ) (t : ℝ) : Polynomial ℂ :=
  fabiusSaddleReferencePolynomial (2 * (N + 1))
    (dyadicLambertPhase t) (dyadicLambertEpsilon t : ℂ)

/-- Gaussian contraction of the order-`N` dyadic Lambert reference
polynomial, for `t` with `0 < dyadicLambertPhase t`.  All odd epsilon-orders
drop out by
`gaussianPolynomialContraction_negativeLaplaceExpCoeff_odd`, and what is
left is the finite mass expansion
`∑_{j < N+1} (dyadicLambertPhase t)⁻¹ ^ j * fabiusSaddleMassCoefficient j
(dyadicLambertPhase t)`, with the epsilon-powers converted by
`dyadicLambertEpsilon_sq`.  Used by `FabiusSaddleMassAllOrders`. -/
theorem gaussianPolynomialContraction_dyadicLambertReferencePolynomial
    (N : ℕ) {t : ℝ} (ht : 0 < dyadicLambertPhase t) :
    gaussianPolynomialContraction (dyadicLambertReferencePolynomial N t) =
      ∑ j ∈ Finset.range (N + 1),
        (dyadicLambertPhase t)⁻¹ ^ j *
          (fabiusSaddleMassCoefficient j (dyadicLambertPhase t) : ℂ) := by
  unfold dyadicLambertReferencePolynomial fabiusSaddleReferencePolynomial
  rw [map_sum, sum_range_two_mul_pair]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.C_mul', Polynomial.C_mul', map_smul, map_smul,
    gaussianPolynomialContraction_negativeLaplaceExpCoeff_odd]
  rw [ofReal_fabiusSaddleMassCoefficient]
  unfold fabiusSaddleMassCoefficientComplex
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [show (dyadicLambertEpsilon t : ℂ) ^ (2 * j) =
      ((dyadicLambertPhase t)⁻¹ : ℂ) ^ j by
    rw [pow_mul, ← Complex.ofReal_pow, dyadicLambertEpsilon_sq ht,
      Complex.ofReal_inv]]
  rw [Complex.ofReal_inv]

/-- Exact exponent left after factoring out the standard Gaussian from the
dyadic Lambert saddle kernel. -/
noncomputable def dyadicLambertCenteredExponent
    (F : BoundedFabius) (t v : ℝ) : ℂ :=
  let b := dyadicLambertPhase t
  let eps := dyadicLambertEpsilon t
  (b : ℂ) * (eps : ℂ) * (v : ℂ) * Complex.I + (v : ℂ) ^ 2 / 2 +
    negativeLaplaceVerticalLog F ((2 : ℝ) ^ b) (eps * v) -
      Complex.log (1 + (((eps * v : ℝ) : ℂ) * Complex.I))

/-- Periodic exponent polynomial truncated through epsilon order `M`. -/
noncomputable def dyadicLambertExponentTruncation
    (M : ℕ) (t v : ℝ) : ℂ :=
  ∑ m ∈ Finset.range (M + 1),
    (dyadicLambertEpsilon t : ℂ) ^ m *
      negativeLaplaceExponentCoefficient m (dyadicLambertPhase t) v

/-- The explicit Taylor sum `negativeLaplaceVerticalTaylorSum F K t eps v`
of the vertical logarithm at radius `2 ^ t` agrees with Mathlib's
`taylorWithinEval` of order `K` for that function, taken within
`uIcc 0 (eps * v)`, based at `0` and evaluated at `eps * v`.  Requires
`IsFabius F`; it holds for all real `t`, `eps` and `v`, the degenerate case
`eps * v = 0` included.  `FabiusSaddleMassAllOrders` rewrites with it to put
the sum in the shape required by
`norm_negativeLaplaceVerticalLog_sub_taylorWithinEval_le`. -/
theorem negativeLaplaceVerticalTaylorSum_eq_taylorWithinEval
    (F : BoundedFabius) (hF : IsFabius F)
    (K : ℕ) (t eps v : ℝ) :
    negativeLaplaceVerticalTaylorSum F K t eps v =
      taylorWithinEval
        (negativeLaplaceVerticalLog F ((2 : ℝ) ^ t)) K
        (uIcc 0 (eps * v)) 0 (eps * v) := by
  by_cases htheta : eps * v = 0
  · rw [htheta]
    rw [taylorWithinEval_self, negativeLaplaceVerticalLog_zero]
    unfold negativeLaplaceVerticalTaylorSum
    apply Finset.sum_eq_zero
    intro k hk
    cases k with
    | zero => simp [negativeLaplaceVerticalLog_zero]
    | succ k =>
        rw [htheta, zero_pow (Nat.succ_ne_zero k), zero_div,
          Complex.ofReal_zero, zero_mul]
  · rw [taylor_within_apply]
    unfold negativeLaplaceVerticalTaylorSum
    apply Finset.sum_congr rfl
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_uIcc (fun h => htheta h.symm))
      ((contDiff_negativeLaplaceVerticalLog_infty F hF
        (Real.rpow_pos_of_pos (by norm_num) t)).contDiffAt.of_le
          (by exact_mod_cast
            (show (k : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
      (left_mem_uIcc)]
    simp only [sub_zero]
    rw [Complex.real_smul]
    push_cast
    ring

/-- Exact all-order decomposition of the centered exponent.  Besides the
periodic truncation, only the vertical/log Taylor remainders, two boundary
jets, and flat forward-product jets remain. -/
theorem dyadicLambertCenteredExponent_sub_truncation_eq
    (F : BoundedFabius) (hF : IsFabius F)
    (M : ℕ) {t v : ℝ} (ht : 0 < dyadicLambertPhase t) :
    dyadicLambertCenteredExponent F t v -
        dyadicLambertExponentTruncation M t v =
      (negativeLaplaceVerticalLog F
          ((2 : ℝ) ^ dyadicLambertPhase t) (dyadicLambertEpsilon t * v) -
        negativeLaplaceVerticalTaylorSum F (M + 2)
          (dyadicLambertPhase t) (dyadicLambertEpsilon t) v) -
      (Complex.log (1 +
          (((dyadicLambertEpsilon t * v : ℝ) : ℂ) * Complex.I)) -
        Complex.logTaylor (M + 3)
          (((dyadicLambertEpsilon t * v : ℝ) : ℂ) * Complex.I)) +
      (dyadicLambertEpsilon t : ℂ) ^ (M + 1) *
        negativeLaplaceExactExponentBoundedTerm (M + 1)
          (dyadicLambertPhase t) v +
      (dyadicLambertEpsilon t : ℂ) ^ (M + 2) *
        negativeLaplaceExactExponentBoundedTerm (M + 2)
          (dyadicLambertPhase t) v -
      ∑ m ∈ Finset.range (M + 1),
        (dyadicLambertEpsilon t : ℂ) ^ m *
          (match m with
          | 0 => 0
          | n + 1 =>
              Complex.I ^ (n + 1) *
                (negativeLaplaceForwardScaledJet n
                  (dyadicLambertPhase t) : ℂ) *
                (v : ℂ) ^ (n + 1) /
                  ((n + 1).factorial : ℕ)) := by
  let b := dyadicLambertPhase t
  let eps := dyadicLambertEpsilon t
  have hscale : (b : ℂ) * (eps : ℂ) ^ 2 = 1 := by
    dsimp [b, eps]
    rw [← Complex.ofReal_pow, dyadicLambertEpsilon_sq ht]
    push_cast
    field_simp [ht.ne']
  have halgebra := centeredJetSum_eq_exactExponentSum_boundary
    M b (eps : ℂ) v hscale
  have hjets := verticalTaylorSum_sub_logTaylor_eq_jetSum
    F hF (M + 2) b eps v
  have hcoeff (m : ℕ) :
      negativeLaplaceExactExponentCoefficient m b v =
        negativeLaplaceExponentCoefficient m b v -
          match m with
          | 0 => 0
          | n + 1 =>
              Complex.I ^ (n + 1) *
                (negativeLaplaceForwardScaledJet n b : ℂ) *
                (v : ℂ) ^ (n + 1) /
                  ((n + 1).factorial : ℕ) :=
    negativeLaplaceExactExponentCoefficient_eq m b v
  dsimp [b, eps] at halgebra hjets hcoeff ⊢
  unfold dyadicLambertCenteredExponent dyadicLambertExponentTruncation
  dsimp only
  rw [← hjets] at halgebra
  simp_rw [hcoeff] at halgebra
  simp_rw [mul_sub] at halgebra
  rw [Finset.sum_sub_distrib] at halgebra
  rw [show M + 2 + 1 = M + 3 by omega] at halgebra
  linear_combination halgebra

/-- Exact Gaussian-times-centered-exponential representation of the dyadic
Lambert kernel. -/
theorem dyadicLambertKernel_eq_gaussian_exp_centered
    (F : BoundedFabius) (hF : IsFabius F)
    {t v : ℝ} (ht : 0 < dyadicLambertPhase t)
    (hsmall : Real.log 2 * (2 : ℝ) ^ (-t) < Real.exp (-1)) :
    SaddleLambert.dyadicLambertKernel F t v =
      QuantitativeSaddle.standardGaussian v *
        Complex.exp (dyadicLambertCenteredExponent F t v) := by
  let b : ℝ := dyadicLambertPhase t
  let x : ℝ := (2 : ℝ) ^ (-t)
  let r : ℝ := (2 : ℝ) ^ b
  let eps : ℝ := dyadicLambertEpsilon t
  let theta : ℝ := eps * v
  let w : ℂ := 1 + (theta : ℂ) * Complex.I
  have hx : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hsaddle : r * x = b := by
    have hs := fabiusLambertRadius_mul_argument
      (x := (2 : ℝ) ^ (-t))
      (Real.rpow_pos_of_pos (by norm_num) _) hsmall
    simpa only [r, x, b, fabiusLambertRadius_dyadic,
      fabiusLambertPhase_dyadic] using hs
  have heps : eps = 1 / Real.sqrt b := by
    dsimp [eps, b]
    rw [dyadicLambertEpsilon, one_div]
  have heps0 : dyadicLambertEpsilon t =
      1 / Real.sqrt (dyadicLambertPhase t) := by
    rw [dyadicLambertEpsilon, one_div]
  have htheta : theta = v / Real.sqrt b := by
    dsimp [theta]
    rw [heps]
    ring
  have hsqrt : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 (by simpa [b] using ht)).ne'
  have hw : w ≠ 0 := by
    apply (norm_one_add_mul_I_pos theta).ne'.comp norm_eq_zero.mpr
  have hcurve0 : negativeLaplaceVerticalCurve F r 0 =
      complexGeneratingFunction F (-(r : ℂ)) := by
    simp [negativeLaplaceVerticalCurve]
  have hcurve : negativeLaplaceVerticalCurve F r theta =
      complexGeneratingFunction F
        (-((r : ℂ) + ((r * v / Real.sqrt b : ℝ) : ℂ) * Complex.I)) := by
    unfold negativeLaplaceVerticalCurve
    congr 2
    rw [htheta]
    push_cast
    ring
  have hratio :
      complexGeneratingFunction F
          (-((r : ℂ) + ((r * v / Real.sqrt b : ℝ) : ℂ) * Complex.I)) /
        complexGeneratingFunction F (-(r : ℂ)) =
      Complex.exp (negativeLaplaceVerticalLog F r theta) := by
    rw [← hcurve, ← hcurve0]
    exact (exp_negativeLaplaceVerticalLog F hF hr theta).symm
  have hden : w⁻¹ = Complex.exp (-Complex.log w) := by
    rw [Complex.exp_neg, Complex.exp_log hw]
  unfold SaddleLambert.dyadicLambertKernel
  rw [fabiusLambertRadius_dyadic]
  change Complex.exp ((((r * x * v / Real.sqrt b : ℝ) : ℂ) * Complex.I)) *
      (complexGeneratingFunction F
          (-((r : ℂ) + ((r * v / Real.sqrt b : ℝ) : ℂ) * Complex.I)) /
        complexGeneratingFunction F (-(r : ℂ))) /
      (1 + ((v / Real.sqrt b : ℝ) : ℂ) * Complex.I) = _
  rw [hratio]
  rw [← htheta]
  change Complex.exp ((((r * x * v / Real.sqrt b : ℝ) : ℂ) * Complex.I)) *
      Complex.exp (negativeLaplaceVerticalLog F r theta) / w = _
  rw [div_eq_mul_inv, hden, ← Complex.exp_add, ← Complex.exp_add]
  rw [show QuantitativeSaddle.standardGaussian v =
      Complex.exp (((-(v ^ 2) / 2 : ℝ) : ℂ)) by
    rw [QuantitativeSaddle.standardGaussian, Complex.ofReal_exp],
    ← Complex.exp_add]
  congr 1
  unfold dyadicLambertCenteredExponent
  dsimp [b, r, eps, theta, w]
  rw [heps0]
  push_cast
  have hsaddleC := congrArg (fun y : ℝ => (y : ℂ)) hsaddle
  push_cast at hsaddleC
  have hsqrtC : ((Real.sqrt b : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsqrt
  dsimp [r, x, b] at hsaddleC hsqrt hsqrtC ⊢
  field_simp [hsqrt, hsqrtC]
  rw [hsaddleC]
  ring

end

end Fabius
