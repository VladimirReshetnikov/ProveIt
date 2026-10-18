import GowersSzemeredi.Section10
import GowersSzemeredi.Sections12_13
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Dist
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.ConditionalProbability
import Mathlib.RingTheory.Coprime.Lemmas

/-! Quantitative margins between the Section 13 recurrence exponents.
Large powers of two are kept symbolic rather than expanded as numerals.

`section13_recurrence_exponent_margin` and `two_rpow_seven_mul_gt` are in
`Proofs13ExponentMarginsSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The lower edge-density parameter gives the Fourier cutoff printed in
Lemma 13.6. -/
theorem section13_lambda_formula {alpha : Real} (hα : 0 < alpha) :
    section10Lambda (alpha ^ 32 / 16) = (2 : Real) ^ (-(59 : Int)) * alpha ^ 176 := by
  unfold section10Lambda
  rw [Real.div_rpow (pow_nonneg hα.le _) (by norm_num),
    ← Real.rpow_natCast_mul hα.le]
  have hden : (16 : Real) ^ ((11 : Real) / 2) = (2 : Real) ^ (22 : Nat) := by
    rw [show (16 : Real) = (2 : Real) ^ (4 : Nat) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num)]
    norm_num
  rw [hden]
  norm_num [Real.rpow_neg, zpow_neg]
  ring

/-- A convenient coarser cutoff, preserving a large margin in the spectral
count bound. -/
theorem section13_lambda_lower {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (2 : Real) ^ (-(64 : Real)) * alpha ^ (192 : Real) ≤
      section10Lambda (alpha ^ 32 / 16) := by
  rw [section13_lambda_formula hα, Real.rpow_ofNat alpha 192]
  have hpow : alpha ^ 192 ≤ alpha ^ 176 := pow_le_pow_of_le_one hα.le hαone (by omega)
  have htwo : (2 : Real) ^ (-(64 : Real)) ≤ (2 : Real) ^ (-(59 : Int)) := by
    rw [← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact mul_le_mul htwo hpow (pow_nonneg hα.le _) (by positivity)

/-- The actual Stage 13.4 spectrum count is at most half the much larger
parameter used in Lemma 13.6. -/
theorem section13_qBound_le_half_Q {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    section13QBound (section10Lambda (alpha ^ 32 / 16)) ≤ section13Q alpha / 2 := by
  let theta := section10Lambda (alpha ^ 32 / 16)
  have hbase : 0 < (2 : Real) ^ (-(64 : Real)) * alpha ^ (192 : Real) := by positivity
  have htheta := section13_lambda_lower hα hαone
  have hrecip : theta ^ (-(10479 : Real)) ≤
      ((2 : Real) ^ (-(64 : Real)) * alpha ^ (192 : Real)) ^ (-(10479 : Real)) :=
    Real.rpow_le_rpow_of_nonpos hbase htheta (by norm_num)
  have hformula : (2 : Real) ^ (1882 : Real) *
      ((2 : Real) ^ (-(64 : Real)) * alpha ^ (192 : Real)) ^ (-(10479 : Real)) =
      (2 : Real) ^ (672538 : Real) * alpha ^ (-(2011968 : Real)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hα.le _),
      ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2), ← Real.rpow_mul hα.le]
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
    congr 1 <;> norm_num
  have hlarge : (2 : Real) ^ (672538 : Real) * alpha ^ (-(2011968 : Real)) ≤
      (2 : Real) ^ (1048575 : Real) * alpha ^ (-(2097152 : Real)) := by
    apply mul_le_mul
    · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    · exact Real.rpow_le_rpow_of_exponent_ge hα hαone (by norm_num)
    · positivity
    · positivity
  have hQ : (2 : Real) ^ (1048575 : Real) * alpha ^ (-(2097152 : Real)) =
      section13Q alpha / 2 := by
    unfold section13Q
    rw [show (2 : Nat) ^ 20 = 1048576 by norm_num,
      show (2 : Real) ^ (21 : Nat) = 2097152 by norm_num, ← Real.rpow_natCast]
    norm_num only [Nat.cast_ofNat]
    rw [show (1048576 : Real) = 1048575 + 1 by norm_num,
      Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one]
    ring
  calc
    _ = (2 : Real) ^ (1882 : Real) * theta ^ (-(10479 : Real)) := by
      unfold section13QBound
      simp only [Real.rpow_ofNat, Real.rpow_neg_ofNat, theta]
    _ ≤ (2 : Real) ^ (1882 : Real) *
        ((2 : Real) ^ (-(64 : Real)) * alpha ^ (192 : Real)) ^ (-(10479 : Real)) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = _ := hformula
    _ ≤ _ := hlarge
    _ = _ := hQ

/-- The two Stage 13.4 parameters have an exact reciprocal relation. -/
theorem section13_thetaOne_qBound_product {theta : Real} (hθ : 0 < theta) :
    section13ThetaOne theta * section13QBound theta = theta ^ (-(2 : Int)) := by
  have htwo : (2 : Real) ^ (1882 : Nat) * (2 : Real) ^ (-(1882 : Int)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
    norm_num
  have ht : theta ^ (-(10479 : Int)) * theta ^ (10477 : Nat) = theta ^ (-(2 : Int)) := by
    rw [← zpow_natCast, ← zpow_add₀ hθ.ne']
    norm_num
  unfold section13ThetaOne section13QBound
  calc
    _ = ((2 : Real) ^ (1882 : Nat) * (2 : Real) ^ (-(1882 : Int))) *
        (theta ^ (-(10479 : Int)) * theta ^ (10477 : Nat)) := by ring
    _ = _ := by rw [htwo, ht, one_mul]

end LeanProofs.GowersSzemeredi
