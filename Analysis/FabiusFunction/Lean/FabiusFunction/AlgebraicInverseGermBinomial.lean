import FabiusFunction.AlgebraicInverseGerm
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# The dyadic germ is the binomial series: all-orders identification

The inverse volume's remaining germ item asked for the all-orders
identification of the formal root with the analytic branch.  Here it
is: the formal quantile germ `Δ₂` — the unique zero-constant root of
`𝒜₂(z,Q) = z + 4z² - (4/9)Q` — equals the explicit binomial series

`Δ₂(Q) = (1/8)·((1 + (64/9)Q)^{1/2} - 1)`,

because the rescaled formal binomial series squares to `1 + (64/9)Q`
(`binomialSeries_add` at `1/2 + 1/2`), so the explicit series is a
zero-constant root, and the root is unique.  Every coefficient of the
germ is thereby in closed form, matching the Taylor coefficients of
the analytic branch of `AlgebraicInverseGermAnalytic`.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

/-- The explicit binomial-series root of the concrete dyadic germ. -/
noncomputable def dyadicBinomialGerm : PowerSeries ℚ :=
  PowerSeries.C ((8 : ℚ)⁻¹) *
    (PowerSeries.rescale ((64 : ℚ) / 9)
      (binomialSeries ℚ ((1 : ℚ) / 2)) - 1)

/-- The rescaled binomial series squares to `1 + (64/9)Q`. -/
theorem sq_rescale_binomial :
    (PowerSeries.rescale ((64 : ℚ) / 9)
        (binomialSeries ℚ ((1 : ℚ) / 2))) ^ 2 =
      1 + PowerSeries.C ((64 : ℚ) / 9) * PowerSeries.X := by
  rw [sq, ← map_mul, ← binomialSeries_add,
    show ((1 : ℚ) / 2 + (1 : ℚ) / 2) = ((1 : ℕ) : ℚ) from by norm_num,
    binomialSeries_nat, pow_one, map_add, map_one]
  congr 1
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X, PowerSeries.coeff_X]
  by_cases h : n = 1 <;> simp [h]

/-- The explicit series has zero constant term. -/
theorem constantCoeff_dyadicBinomialGerm :
    PowerSeries.constantCoeff dyadicBinomialGerm = 0 := by
  have hS0 : PowerSeries.constantCoeff
      (PowerSeries.rescale ((64 : ℚ) / 9)
        (binomialSeries ℚ ((1 : ℚ) / 2))) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      binomialSeries_constantCoeff]
  rw [dyadicBinomialGerm, map_mul, map_sub, map_one, hS0, sub_self,
    mul_zero]

/-- The explicit series solves the concrete germ equation. -/
theorem dyadicBinomialGerm_solves :
    dyadicBinomialGerm + 4 * dyadicBinomialGerm ^ 2 =
      PowerSeries.C ((4 : ℚ) / 9) * PowerSeries.X := by
  have hlin : (8 : PowerSeries ℚ) * dyadicBinomialGerm =
      PowerSeries.rescale ((64 : ℚ) / 9)
        (binomialSeries ℚ ((1 : ℚ) / 2)) - 1 := by
    rw [dyadicBinomialGerm,
      show (8 : PowerSeries ℚ) = PowerSeries.C (8 : ℚ) from by simp,
      ← mul_assoc, ← map_mul,
      show (8 : ℚ) * (8 : ℚ)⁻¹ = 1 from by norm_num, map_one,
      one_mul]
  have h9sq : (9 : PowerSeries ℚ) *
      (PowerSeries.rescale ((64 : ℚ) / 9)
        (binomialSeries ℚ ((1 : ℚ) / 2))) ^ 2 =
      9 + 64 * PowerSeries.X := by
    rw [sq_rescale_binomial, mul_add, mul_one,
      show (9 : PowerSeries ℚ) = PowerSeries.C (9 : ℚ) from by simp,
      ← mul_assoc, ← map_mul,
      show (9 : ℚ) * ((64 : ℚ) / 9) = (64 : ℚ) from by norm_num]
    congr 1
    · simp
    · congr 1
      simp
  have h144 : (144 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.constantCoeff) h
    rw [map_ofNat, map_zero] at hc
    exact absurd hc (by norm_num)
  have hRHS : (144 : PowerSeries ℚ) *
      (PowerSeries.C ((4 : ℚ) / 9) * PowerSeries.X) =
      64 * PowerSeries.X := by
    rw [show (144 : PowerSeries ℚ) = PowerSeries.C (144 : ℚ) from by
        simp,
      ← mul_assoc, ← map_mul,
      show (144 : ℚ) * ((4 : ℚ) / 9) = (64 : ℚ) from by norm_num]
    congr 1
    simp
  refine mul_left_cancel₀ h144 ?_
  rw [hRHS]
  linear_combination (9 * (8 * dyadicBinomialGerm + 1 +
      PowerSeries.rescale ((64 : ℚ) / 9)
        (binomialSeries ℚ ((1 : ℚ) / 2)))) * hlin + h9sq

/-- The first derivative of the terminating jet. -/
theorem derivative_dyadicJetTwo :
    Polynomial.derivative dyadicJetTwo = 1 + 8 * Polynomial.X := by
  rw [dyadicJetTwo]
  simp
  ring

/-- The second derivative of the terminating jet is the constant 8. -/
theorem derivative_two_dyadicJetTwo :
    Polynomial.derivative^[2 * 1] dyadicJetTwo = 8 := by
  show Polynomial.derivative (Polynomial.derivative dyadicJetTwo) = 8
  rw [derivative_dyadicJetTwo]
  simp

/-- The germ polynomial `𝒜₂` evaluates as `S + 4S² - (4/9)Q`. -/
theorem germPolynomial_dyadicTwo_eval (S : PowerSeries ℚ) :
    (germPolynomial dyadicWeightsTwo dyadicJetTwo).eval S =
      S + 4 * S ^ 2 -
        PowerSeries.C ((4 : ℚ) / 9) * PowerSeries.X := by
  have hdeg : dyadicJetTwo.natDegree ≤ 2 := by
    rw [dyadicJetTwo]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact (Polynomial.natDegree_smul_le _ _).trans (by simp)
  rw [germPolynomial_eq_sum dyadicWeightsTwo dyadicJetTwo hdeg]
  rw [Finset.sum_range_succ, Finset.sum_range_one,
    derivative_two_dyadicJetTwo]
  rw [Polynomial.eval_add, Polynomial.eval_smul, Polynomial.eval_smul]
  have hw0 : dyadicWeightsTwo 0 = 1 := by
    simp [dyadicWeightsTwo]
  have hw1 : dyadicWeightsTwo 1 = -(1 / 18 : ℚ) := by
    simp [dyadicWeightsTwo]
  rw [hw0, hw1]
  have hJeval : ((Function.iterate Polynomial.derivative (2 * 0)
      dyadicJetTwo).map (PowerSeries.C)).eval S = S + 4 * S ^ 2 := by
    show ((dyadicJetTwo).map (PowerSeries.C)).eval S = S + 4 * S ^ 2
    rw [dyadicJetTwo]
    simp [Polynomial.eval_map]
    ring
  have h8eval : (((8 : Polynomial ℚ)).map
      (PowerSeries.C : ℚ →+* PowerSeries ℚ)).eval S = 8 := by
    simp
  rw [hJeval, h8eval]
  have hfold : (PowerSeries.C (-(1 / 18 : ℚ)) * PowerSeries.X) •
      (8 : PowerSeries ℚ) =
      -(PowerSeries.C ((4 : ℚ) / 9) * PowerSeries.X) := by
    rw [smul_eq_mul,
      show (8 : PowerSeries ℚ) = PowerSeries.C (8 : ℚ) from by simp,
      mul_right_comm, ← map_mul,
      show (-(1 / 18 : ℚ)) * 8 = -((4 : ℚ) / 9) from by norm_num,
      map_neg, neg_mul]
  rw [hfold]
  have hone : (PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0) •
      (S + 4 * S ^ 2) = S + 4 * S ^ 2 := by
    rw [map_one, pow_zero, mul_one, one_smul]
  rw [hone]
  ring

/-- **All-orders identification**: the formal quantile germ is the
explicit binomial series `(1/8)·((1 + (64/9)Q)^{1/2} - 1)`. -/
theorem dyadicGermTwo_eq_binomial :
    dyadicGermTwo = dyadicBinomialGerm := by
  obtain ⟨S, _hS, huniq⟩ := existsUnique_dyadicGermTwo
  have h1 := huniq dyadicGermTwo
    ⟨constantCoeff_germRoot _ _ _ _ _, eval_germRoot _ _ _ _ _⟩
  have h2 := huniq dyadicBinomialGerm
    ⟨constantCoeff_dyadicBinomialGerm, by
      rw [germPolynomial_dyadicTwo_eval, dyadicBinomialGerm_solves,
        sub_self]⟩
  rw [h1, h2]

/-- Closed form of every positive-order germ coefficient:
`[Qⁿ]Δ₂ = (1/8)·C(1/2,n)·(64/9)ⁿ`. -/
theorem coeff_dyadicGermTwo_of_pos {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n dyadicGermTwo =
      (8 : ℚ)⁻¹ * (Ring.choose ((1 : ℚ) / 2) n * ((64 : ℚ) / 9) ^ n) := by
  rw [dyadicGermTwo_eq_binomial, dyadicBinomialGerm,
    PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_rescale,
    binomialSeries_coeff]
  rw [PowerSeries.coeff_one, if_neg (by omega)]
  rw [smul_eq_mul, mul_one, sub_zero]
  ring

end Fabius
