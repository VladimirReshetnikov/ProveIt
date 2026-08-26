import FabiusFunction.AnalyticMoments
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The negative Laplace product and its exact periodic decomposition

For `s > 0`, iteration of the half-moment generating-function equation gives

`G(-s) = ∏ j ≥ 1, (1 - exp (-s / 2^j)) / (s / 2^j)`.

This file constructs the logarithm of that product directly as an absolutely
convergent series.  Splitting its dilation equation into a quadratic solution
and a forward tail produces an *exact* one-periodic correction.  In
particular, the logarithm is

`-(log s)^2 / (2 log 2) + (log s) / 2 + R(log₂ s) + E(s)`,

where `R(t + 1) = R(t)` and `|E(s)| ≤ exp(-s) / (1 - exp(-s))^2`.
The last bound is at most `4 exp(-s)` once `s ≥ log 2`.

The construction uses only elementary real logarithm and exponential bounds;
it does not rely on Mellin inversion or vertical estimates for `Gamma`.
The sign information implicit in the product is exposed as well: every
logarithmic factor, the full logarithmic product, and the forward tail are
nonpositive, while the tail error obtained by negating the forward tail is
nonnegative.
-/

set_option autoImplicit false

open scoped BigOperators
open Filter Topology

namespace Fabius

/-- The logarithm of one factor in the negative Laplace product. -/
noncomputable def negativeLaplaceKernel (x : ℝ) : ℝ :=
  Real.log ((1 - Real.exp (-x)) / x)

private lemma exp_neg_le_one_sub_div (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) ≤ (1 - Real.exp (-x)) / x := by
  rw [le_div_iff₀ hx]
  have h := Real.add_one_le_exp x
  have he : 0 < Real.exp (-x) := Real.exp_pos _
  rw [Real.exp_neg] at he ⊢
  field_simp
  nlinarith

private lemma one_sub_exp_neg_div_le_one (x : ℝ) (hx : 0 < x) :
    (1 - Real.exp (-x)) / x ≤ 1 := by
  rw [div_le_one hx]
  have h := Real.add_one_le_exp (-x)
  linarith

/-- Every logarithmic product factor is nonpositive. -/
theorem negativeLaplaceKernel_nonpos (x : ℝ) (hx : 0 < x) :
    negativeLaplaceKernel x ≤ 0 := by
  apply Real.log_nonpos
  · exact (Real.exp_pos _).le.trans (exp_neg_le_one_sub_div x hx)
  · exact one_sub_exp_neg_div_le_one x hx

/-- Every logarithmic product factor is in fact strictly negative at positive
arguments. -/
theorem negativeLaplaceKernel_neg (x : ℝ) (hx : 0 < x) :
    negativeLaplaceKernel x < 0 := by
  rw [negativeLaplaceKernel]
  apply Real.log_neg
  · apply div_pos
    · apply sub_pos.mpr
      simpa using Real.exp_lt_exp.mpr (neg_lt_zero.mpr hx)
    · exact hx
  · rw [div_lt_one hx]
    nlinarith [Real.add_one_lt_exp (neg_ne_zero.mpr hx.ne')]

/-- Elementary lower bound for a logarithmic product factor. -/
theorem neg_le_negativeLaplaceKernel (x : ℝ) (hx : 0 < x) :
    -x ≤ negativeLaplaceKernel x := by
  rw [negativeLaplaceKernel, Real.le_log_iff_exp_le]
  · simpa using exp_neg_le_one_sub_div x hx
  · exact (Real.exp_pos _).trans_le (exp_neg_le_one_sub_div x hx)

/-- Absolute convergence bound for one logarithmic product factor. -/
theorem abs_negativeLaplaceKernel_le (x : ℝ) (hx : 0 < x) :
    |negativeLaplaceKernel x| ≤ x := by
  rw [abs_of_nonpos (negativeLaplaceKernel_nonpos x hx)]
  linarith [neg_le_negativeLaplaceKernel x hx]

/-- The `n`th factor, corresponding to the scale `s / 2^(n+1)`. -/
noncomputable def negativeLaplaceTerm (s : ℝ) (n : ℕ) : ℝ :=
  negativeLaplaceKernel (s / (2 : ℝ) ^ (n + 1))

/-- A geometric majorant for the logarithmic product series. -/
theorem abs_negativeLaplaceTerm_le (s : ℝ) (hs : 0 < s) (n : ℕ) :
    |negativeLaplaceTerm s n| ≤ s / 2 / 2 ^ n := by
  rw [negativeLaplaceTerm]
  have hp : 0 < s / (2 : ℝ) ^ (n + 1) := by positivity
  refine (abs_negativeLaplaceKernel_le _ hp).trans_eq ?_
  rw [pow_succ]
  ring

/-- Every term of the logarithmic product series is nonpositive. -/
theorem negativeLaplaceTerm_nonpos (s : ℝ) (hs : 0 < s) (n : ℕ) :
    negativeLaplaceTerm s n ≤ 0 := by
  exact negativeLaplaceKernel_nonpos _ (by positivity)

/-- Every term of the logarithmic product series is strictly negative. -/
theorem negativeLaplaceTerm_neg (s : ℝ) (hs : 0 < s) (n : ℕ) :
    negativeLaplaceTerm s n < 0 := by
  exact negativeLaplaceKernel_neg _ (by positivity)

/-- The logarithmic product series is absolutely summable for `s > 0`. -/
theorem summable_negativeLaplaceTerm (s : ℝ) (hs : 0 < s) :
    Summable (negativeLaplaceTerm s) := by
  exact (summable_geometric_two' s).of_norm_bounded
    (abs_negativeLaplaceTerm_le s hs)

/-- Logarithm of the canonical negative Laplace product. -/
noncomputable def negativeLaplaceLog (s : ℝ) : ℝ :=
  ∑' n : ℕ, negativeLaplaceTerm s n

/-- The logarithm of the negative Laplace product is nonpositive on the
positive half-line. -/
theorem negativeLaplaceLog_nonpos (s : ℝ) (hs : 0 < s) :
    negativeLaplaceLog s ≤ 0 := by
  exact tsum_nonpos (negativeLaplaceTerm_nonpos s hs)

/-- The logarithm of the negative Laplace product is strictly negative on the
positive half-line. -/
theorem negativeLaplaceLog_neg (s : ℝ) (hs : 0 < s) :
    negativeLaplaceLog s < 0 := by
  rw [negativeLaplaceLog]
  have hlt := Summable.tsum_lt_tsum (i := 0)
    (negativeLaplaceTerm_nonpos s hs) (negativeLaplaceTerm_neg s hs 0)
    (summable_negativeLaplaceTerm s hs) summable_zero
  simpa using hlt

private lemma negativeLaplaceTerm_two_zero (s : ℝ) :
    negativeLaplaceTerm (2 * s) 0 = negativeLaplaceKernel s := by
  simp [negativeLaplaceTerm]

private lemma negativeLaplaceTerm_two_succ (s : ℝ) (n : ℕ) :
    negativeLaplaceTerm (2 * s) (n + 1) = negativeLaplaceTerm s n := by
  simp only [negativeLaplaceTerm]
  apply congrArg negativeLaplaceKernel
  rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
  ring

/-- Exact dilation equation for the logarithmic product. -/
theorem negativeLaplaceLog_two_mul (s : ℝ) (hs : 0 < s) :
    negativeLaplaceLog (2 * s) =
      negativeLaplaceKernel s + negativeLaplaceLog s := by
  rw [negativeLaplaceLog,
    (summable_negativeLaplaceTerm (2 * s) (by positivity)).tsum_eq_zero_add]
  simp_rw [negativeLaplaceTerm_two_zero, negativeLaplaceTerm_two_succ]
  rfl

/-- One term of the forward tail used to periodize the dilation equation. -/
noncomputable def negativeLaplaceForwardTerm (s : ℝ) (n : ℕ) : ℝ :=
  Real.log (1 - Real.exp (-(s * (2 : ℝ) ^ n)))

private lemma exp_neg_lt_one (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) < 1 := by
  simpa using Real.exp_lt_exp.mpr (show -x < 0 by linarith)

private lemma abs_log_one_sub_exp_neg_le (x : ℝ) (hx : 0 < x) :
    |Real.log (1 - Real.exp (-x))| ≤
      Real.exp (-x) / (1 - Real.exp (-x)) := by
  have he0 : 0 < Real.exp (-x) := Real.exp_pos _
  have he1 : Real.exp (-x) < 1 := exp_neg_lt_one x hx
  have hd : 0 < 1 - Real.exp (-x) := sub_pos.mpr he1
  rw [abs_of_nonpos (Real.log_nonpos hd.le (by linarith))]
  calc
    -Real.log (1 - Real.exp (-x)) =
        Real.log (1 - Real.exp (-x))⁻¹ := by rw [Real.log_inv]
    _ ≤ (1 - Real.exp (-x))⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
    _ = Real.exp (-x) / (1 - Real.exp (-x)) := by
      field_simp
      ring

/-- Every term of the forward logarithmic tail is nonpositive. -/
theorem negativeLaplaceForwardTerm_nonpos
    (s : ℝ) (hs : 0 < s) (n : ℕ) :
    negativeLaplaceForwardTerm s n ≤ 0 := by
  rw [negativeLaplaceForwardTerm]
  apply Real.log_nonpos
  · have hp : 0 < s * (2 : ℝ) ^ n := by positivity
    exact (sub_pos.mpr (exp_neg_lt_one _ hp)).le
  · linarith [Real.exp_pos (-(s * (2 : ℝ) ^ n))]

/-- Every term of the forward logarithmic tail is strictly negative. -/
theorem negativeLaplaceForwardTerm_neg
    (s : ℝ) (hs : 0 < s) (n : ℕ) :
    negativeLaplaceForwardTerm s n < 0 := by
  rw [negativeLaplaceForwardTerm]
  apply Real.log_neg
  · have hp : 0 < s * (2 : ℝ) ^ n := by positivity
    exact sub_pos.mpr (exp_neg_lt_one _ hp)
  · linarith [Real.exp_pos (-(s * (2 : ℝ) ^ n))]

private lemma exp_forward_le_geometric (s : ℝ) (hs : 0 < s) (n : ℕ) :
    Real.exp (-(s * (2 : ℝ) ^ n)) ≤ Real.exp (-s) ^ (n + 1) := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hn : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    have hnat : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt Nat.lt_two_pow_self
    exact_mod_cast hnat
  nlinarith

/-- A geometric majorant for one forward-tail term. -/
theorem abs_negativeLaplaceForwardTerm_le
    (s : ℝ) (hs : 0 < s) (n : ℕ) :
    |negativeLaplaceForwardTerm s n| ≤
      Real.exp (-s) ^ (n + 1) / (1 - Real.exp (-s)) := by
  rw [negativeLaplaceForwardTerm]
  have hp : 0 < s * (2 : ℝ) ^ n := by positivity
  refine (abs_log_one_sub_exp_neg_le _ hp).trans ?_
  have hnum := exp_forward_le_geometric s hs n
  have hden : 0 < 1 - Real.exp (-s) := sub_pos.mpr (exp_neg_lt_one s hs)
  have hexp : Real.exp (-(s * (2 : ℝ) ^ n)) ≤ Real.exp (-s) := by
    apply Real.exp_le_exp.mpr
    have hp' : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hden' : 1 - Real.exp (-s) ≤
      1 - Real.exp (-(s * (2 : ℝ) ^ n)) := sub_le_sub_left hexp 1
  exact (div_le_div_of_nonneg_left (Real.exp_nonneg _) hden hden').trans
    (div_le_div_of_nonneg_right hnum hden.le)

/-- The forward-tail series is absolutely summable for `s > 0`. -/
theorem summable_negativeLaplaceForwardTerm (s : ℝ) (hs : 0 < s) :
    Summable (negativeLaplaceForwardTerm s) := by
  have hr0 : 0 ≤ Real.exp (-s) := Real.exp_nonneg _
  have hr1 : Real.exp (-s) < 1 := exp_neg_lt_one s hs
  have hgeom : Summable (fun n : ℕ => Real.exp (-s) ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  have hmajor : Summable
      (fun n : ℕ => Real.exp (-s) ^ (n + 1) / (1 - Real.exp (-s))) := by
    refine (hgeom.mul_left
      (Real.exp (-s) / (1 - Real.exp (-s)))).congr ?_
    intro n
    rw [pow_succ']
    ring
  exact hmajor.of_norm_bounded (abs_negativeLaplaceForwardTerm_le s hs)

/-- The forward logarithmic tail.  Its terms, and hence its sum, are negative. -/
noncomputable def negativeLaplaceForwardTail (s : ℝ) : ℝ :=
  ∑' n : ℕ, negativeLaplaceForwardTerm s n

/-- The forward logarithmic tail is nonpositive on the positive half-line. -/
theorem negativeLaplaceForwardTail_nonpos (s : ℝ) (hs : 0 < s) :
    negativeLaplaceForwardTail s ≤ 0 := by
  exact tsum_nonpos (negativeLaplaceForwardTerm_nonpos s hs)

/-- The forward logarithmic tail is strictly negative on the positive
half-line. -/
theorem negativeLaplaceForwardTail_neg (s : ℝ) (hs : 0 < s) :
    negativeLaplaceForwardTail s < 0 := by
  rw [negativeLaplaceForwardTail]
  have hlt := Summable.tsum_lt_tsum (i := 0)
    (negativeLaplaceForwardTerm_nonpos s hs)
    (negativeLaplaceForwardTerm_neg s hs 0)
    (summable_negativeLaplaceForwardTerm s hs) summable_zero
  simpa using hlt

private lemma negativeLaplaceForwardTerm_zero (s : ℝ) :
    negativeLaplaceForwardTerm s 0 = Real.log (1 - Real.exp (-s)) := by
  simp [negativeLaplaceForwardTerm]

private lemma negativeLaplaceForwardTerm_two_mul (s : ℝ) (n : ℕ) :
    negativeLaplaceForwardTerm (2 * s) n =
      negativeLaplaceForwardTerm s (n + 1) := by
  simp only [negativeLaplaceForwardTerm]
  congr 3
  rw [pow_succ]
  ring

/-- Exact shift equation for the forward tail. -/
theorem negativeLaplaceForwardTail_two_mul (s : ℝ) (hs : 0 < s) :
    negativeLaplaceForwardTail (2 * s) =
      negativeLaplaceForwardTail s - Real.log (1 - Real.exp (-s)) := by
  rw [negativeLaplaceForwardTail, negativeLaplaceForwardTail,
    (summable_negativeLaplaceForwardTerm s hs).tsum_eq_zero_add]
  simp_rw [negativeLaplaceForwardTerm_zero,
    ← negativeLaplaceForwardTerm_two_mul]
  ring

/-- Explicit absolute bound for the forward tail. -/
theorem abs_negativeLaplaceForwardTail_le (s : ℝ) (hs : 0 < s) :
    |negativeLaplaceForwardTail s| ≤
      Real.exp (-s) / (1 - Real.exp (-s)) ^ 2 := by
  let r := Real.exp (-s)
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := exp_neg_lt_one s hs
  have hmajor : Summable (fun n : ℕ => r ^ (n + 1) / (1 - r)) := by
    have hgeom : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hr0 hr1
    refine (hgeom.mul_left (r / (1 - r))).congr ?_
    intro n
    rw [pow_succ']
    ring
  calc
    |negativeLaplaceForwardTail s| =
        ‖∑' n : ℕ, negativeLaplaceForwardTerm s n‖ := by rfl
    _ ≤ ∑' n : ℕ, ‖negativeLaplaceForwardTerm s n‖ :=
      norm_tsum_le_tsum_norm (summable_negativeLaplaceForwardTerm s hs).norm
    _ ≤ ∑' n : ℕ, r ^ (n + 1) / (1 - r) := by
      exact Summable.tsum_le_tsum
        (fun n => by
          simpa [Real.norm_eq_abs, r] using
            abs_negativeLaplaceForwardTerm_le s hs n)
        (summable_negativeLaplaceForwardTerm s hs).norm hmajor
    _ = r / (1 - r) ^ 2 := by
      rw [show (fun n : ℕ => r ^ (n + 1) / (1 - r)) =
          fun n : ℕ => (r / (1 - r)) * r ^ n by
        funext n
        rw [pow_succ']
        ring]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      field_simp
    _ = Real.exp (-s) / (1 - Real.exp (-s)) ^ 2 := rfl

/-- The positive exponentially small error in the exact decomposition. -/
noncomputable def negativeLaplaceTailError (s : ℝ) : ℝ :=
  -negativeLaplaceForwardTail s

/-- The forward-tail error is nonnegative. -/
theorem negativeLaplaceTailError_nonneg (s : ℝ) (hs : 0 < s) :
    0 ≤ negativeLaplaceTailError s := by
  simpa only [negativeLaplaceTailError, neg_nonneg] using
    negativeLaplaceForwardTail_nonpos s hs

/-- The forward-tail error is strictly positive on the positive half-line. -/
theorem negativeLaplaceTailError_pos (s : ℝ) (hs : 0 < s) :
    0 < negativeLaplaceTailError s := by
  rw [negativeLaplaceTailError, neg_pos]
  exact negativeLaplaceForwardTail_neg s hs

/-- On the positive half-line the absolute value of the tail error can be
removed, since that error is nonnegative. -/
theorem abs_negativeLaplaceTailError (s : ℝ) (hs : 0 < s) :
    |negativeLaplaceTailError s| = negativeLaplaceTailError s :=
  abs_of_nonneg (negativeLaplaceTailError_nonneg s hs)

/-- Global explicit bound for the positive tail error. -/
theorem abs_negativeLaplaceTailError_le (s : ℝ) (hs : 0 < s) :
    |negativeLaplaceTailError s| ≤
      Real.exp (-s) / (1 - Real.exp (-s)) ^ 2 := by
  simpa [negativeLaplaceTailError] using
    abs_negativeLaplaceForwardTail_le s hs

/-- A simpler exponential estimate valid beyond `log 2`. -/
theorem abs_negativeLaplaceTailError_le_four_exp
    (s : ℝ) (hs : Real.log 2 ≤ s) :
    |negativeLaplaceTailError s| ≤ 4 * Real.exp (-s) := by
  have hs0 : 0 < s := (Real.log_pos (by norm_num)).trans_le hs
  refine (abs_negativeLaplaceTailError_le s hs0).trans ?_
  have hr0 : 0 ≤ Real.exp (-s) := Real.exp_nonneg _
  have hrhalf : Real.exp (-s) ≤ 1 / 2 := by
    calc
      Real.exp (-s) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hden : 0 < 1 - Real.exp (-s) := sub_pos.mpr (exp_neg_lt_one s hs0)
  have hsq : 1 ≤ 4 * (1 - Real.exp (-s)) ^ 2 := by nlinarith
  rw [div_le_iff₀ (sq_pos_of_pos hden)]
  calc
    Real.exp (-s) = Real.exp (-s) * 1 := by ring
    _ ≤ Real.exp (-s) * (4 * (1 - Real.exp (-s)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hr0
    _ = 4 * Real.exp (-s) * (1 - Real.exp (-s)) ^ 2 := by ring

/-- For `0 < s`, the logarithmic Laplace factor splits into its numerator and
scale logarithms:
`negativeLaplaceKernel s = Real.log (1 - Real.exp (-s)) - Real.log s`. -/
theorem negativeLaplaceKernel_eq_log_sub_log (s : ℝ) (hs : 0 < s) :
    negativeLaplaceKernel s =
      Real.log (1 - Real.exp (-s)) - Real.log s := by
  have hnum : 1 - Real.exp (-s) ≠ 0 :=
    (sub_pos.mpr (exp_neg_lt_one s hs)).ne'
  rw [negativeLaplaceKernel, Real.log_div hnum hs.ne']

/-- A multiplicatively periodic form of the correction. -/
noncomputable def negativeLaplaceMultiplicativeCorrection (s : ℝ) : ℝ :=
  let t := Real.logb 2 s
  negativeLaplaceLog s + Real.log 2 / 2 * (t ^ 2 - t) +
    negativeLaplaceForwardTail s

private lemma logb_two_mul (s : ℝ) (hs : 0 < s) :
    Real.logb 2 (2 * s) = Real.logb 2 s + 1 := by
  rw [Real.logb_mul (by norm_num) hs.ne']
  rw [Real.logb_self_eq_one (by norm_num)]
  ring

private lemma log_eq_log_two_mul_logb_two (s : ℝ) :
    Real.log s = Real.log 2 * Real.logb 2 s := by
  rw [Real.logb]
  field_simp

/-- The correction is invariant under multiplication of its argument by two. -/
theorem negativeLaplaceMultiplicativeCorrection_two_mul
    (s : ℝ) (hs : 0 < s) :
    negativeLaplaceMultiplicativeCorrection (2 * s) =
      negativeLaplaceMultiplicativeCorrection s := by
  rw [negativeLaplaceMultiplicativeCorrection,
    negativeLaplaceMultiplicativeCorrection]
  rw [negativeLaplaceLog_two_mul s hs,
    negativeLaplaceForwardTail_two_mul s hs, logb_two_mul s hs,
    negativeLaplaceKernel_eq_log_sub_log s hs,
    log_eq_log_two_mul_logb_two s]
  ring

/-- The additive, one-periodic correction in logarithmic scale. -/
noncomputable def negativeLaplacePeriodicCorrection (t : ℝ) : ℝ :=
  negativeLaplaceMultiplicativeCorrection ((2 : ℝ) ^ t)

/-- Exact one-periodicity of the correction. -/
theorem negativeLaplacePeriodicCorrection_add_one (t : ℝ) :
    negativeLaplacePeriodicCorrection (t + 1) =
      negativeLaplacePeriodicCorrection t := by
  rw [negativeLaplacePeriodicCorrection, negativeLaplacePeriodicCorrection,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num
  rw [mul_comm]
  exact negativeLaplaceMultiplicativeCorrection_two_mul _
    (Real.rpow_pos_of_pos (by norm_num) _)

private lemma negativeLaplacePeriodicCorrection_logb
    (s : ℝ) (hs : 0 < s) :
    negativeLaplacePeriodicCorrection (Real.logb 2 s) =
      negativeLaplaceMultiplicativeCorrection s := by
  rw [negativeLaplacePeriodicCorrection,
    Real.rpow_logb_eq_abs (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1) hs.ne']
  rw [abs_of_pos hs]

/-- Exact quadratic-plus-periodic decomposition of the Laplace logarithm. -/
theorem negativeLaplaceLog_exact_periodic_decomposition
    (s : ℝ) (hs : 0 < s) :
    negativeLaplaceLog s =
      -(Real.log s) ^ 2 / (2 * Real.log 2) + Real.log s / 2 +
        negativeLaplacePeriodicCorrection (Real.logb 2 s) +
          negativeLaplaceTailError s := by
  rw [negativeLaplacePeriodicCorrection_logb s hs,
    negativeLaplaceMultiplicativeCorrection, negativeLaplaceTailError]
  rw [Real.logb]
  have hlogtwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp
  ring

/-- The real half-moment generating function is continuous on the whole real
line. -/
theorem continuous_generatingFunction
    (F : BoundedFabius) (hF : IsFabius F) :
    Continuous (generatingFunction F) := by
  unfold generatingFunction
  apply continuous_const.add
  apply continuous_id.mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous fun p : ℝ × ℝ =>
    rvachevUp F p.2 * Real.exp (p.1 * p.2)
  exact ((rvachev_contDiff F hF).continuous.comp continuous_snd).mul
    (Real.continuous_exp.comp (continuous_fst.mul continuous_snd))

private lemma exp_negativeLaplaceKernel (x : ℝ) (hx : 0 < x) :
    Real.exp (negativeLaplaceKernel x) =
      (1 - Real.exp (-x)) / x := by
  rw [negativeLaplaceKernel, Real.exp_log]
  exact (Real.exp_pos _).trans_le (exp_neg_le_one_sub_div x hx)

private lemma expm1Div_neg (x : ℝ) (hx : 0 < x) :
    expm1Div (-x) = (1 - Real.exp (-x)) / x := by
  rw [expm1Div_of_ne (neg_ne_zero.mpr hx.ne')]
  ring

private lemma generatingFunction_neg_eq_partial
    (F : BoundedFabius) (hF : IsFabius F)
    (s : ℝ) (hs : 0 < s) (N : ℕ) :
    generatingFunction F (-s) =
      Real.exp (∑ n ∈ Finset.range N, negativeLaplaceTerm s n) *
        generatingFunction F (-(s / (2 : ℝ) ^ N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [ih, Finset.sum_range_succ, Real.exp_add]
      have hx : 0 < s / (2 : ℝ) ^ (N + 1) := by positivity
      have hscale := proposition_two_real_formula F hF
        (-(s / (2 : ℝ) ^ (N + 1)))
      have harg : 2 * (-(s / (2 : ℝ) ^ (N + 1))) =
          -(s / (2 : ℝ) ^ N) := by
        rw [pow_succ]
        ring
      rw [harg, expm1Div_neg _ hx] at hscale
      rw [hscale, negativeLaplaceTerm, exp_negativeLaplaceKernel _ hx]
      ring

/-- The logarithmic product is the negative generating/Laplace transform. -/
theorem exp_negativeLaplaceLog_eq_generatingFunction_neg
    (F : BoundedFabius) (hF : IsFabius F) (s : ℝ) (hs : 0 < s) :
    Real.exp (negativeLaplaceLog s) = generatingFunction F (-s) := by
  have hsum : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, negativeLaplaceTerm s n)
      atTop (𝓝 (negativeLaplaceLog s)) :=
    (summable_negativeLaplaceTerm s hs).hasSum.tendsto_sum_nat
  have hexp : Tendsto
      (fun N : ℕ => Real.exp
        (∑ n ∈ Finset.range N, negativeLaplaceTerm s n))
      atTop (𝓝 (Real.exp (negativeLaplaceLog s))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hsum
  have hpow : Tendsto (fun N : ℕ => ((1 / 2 : ℝ) ^ N))
      atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : Tendsto (fun N : ℕ => -(s / (2 : ℝ) ^ N))
      atTop (𝓝 0) := by
    have hmul : Tendsto (fun N : ℕ => s * (1 / 2 : ℝ) ^ N)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hpow)
    convert hmul.neg using 1
    · funext N
      rw [one_div, inv_pow]
      ring
    · simp
  have hgen : Tendsto
      (fun N : ℕ => generatingFunction F (-(s / (2 : ℝ) ^ N)))
      atTop (𝓝 1) := by
    have hc := (continuous_generatingFunction F hF).continuousAt.tendsto.comp hsmall
    have hzero : generatingFunction F 0 = 1 := by simp [generatingFunction]
    change Tendsto
      (generatingFunction F ∘ fun N : ℕ => -(s / (2 : ℝ) ^ N))
      atTop (𝓝 1)
    rw [← hzero]
    exact hc
  have hprod := hexp.mul hgen
  have hconst : Tendsto (fun _N : ℕ => generatingFunction F (-s))
      atTop (𝓝 (generatingFunction F (-s))) := tendsto_const_nhds
  have heq : (fun _N : ℕ => generatingFunction F (-s)) =
      fun N : ℕ =>
        Real.exp (∑ n ∈ Finset.range N, negativeLaplaceTerm s n) *
          generatingFunction F (-(s / (2 : ℝ) ^ N)) := by
    funext N
    exact generatingFunction_neg_eq_partial F hF s hs N
  rw [heq] at hconst
  simpa using tendsto_nhds_unique hprod hconst

/-- On the negative real axis, the generating function is strictly positive:
it is the exponential of the exact negative-Laplace logarithm. -/
lemma generatingFunction_neg_pos
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) (hr : 0 < r) :
    0 < generatingFunction F (-r) := by
  rw [← exp_negativeLaplaceLog_eq_generatingFunction_neg F hF r hr]
  exact Real.exp_pos _

/-- On the nonnegative real axis, the generating function is at least one.

This estimate uses only the nonnegativity of Rvachev's bump and of the real
exponential; no functional equation for `F` is needed. -/
theorem one_le_generatingFunction_of_nonneg
    (F : BoundedFabius) (x : ℝ) (hx : 0 ≤ x) :
    1 ≤ generatingFunction F x := by
  unfold generatingFunction
  have hIntegral :
      0 ≤ ∫ t in (0 : ℝ)..1, rvachevUp F t * Real.exp (x * t) :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ht =>
      mul_nonneg (rvachevUp_nonneg F t) (Real.exp_pos _).le
  exact le_add_of_nonneg_right (mul_nonneg hx hIntegral)

/-- The real generating function is strictly positive everywhere.

For a negative argument this is the exponential-product identity above; for
a nonnegative argument the defining interval integral is nonnegative, so the
generating function is at least one. -/
theorem generatingFunction_pos
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    0 < generatingFunction F x := by
  rcases lt_or_ge x 0 with hx | hx
  · have hneg : 0 < -x := neg_pos.mpr hx
    simpa only [neg_neg] using generatingFunction_neg_pos F hF (-x) hneg
  · exact zero_lt_one.trans_le (one_le_generatingFunction_of_nonneg F x hx)

end Fabius
