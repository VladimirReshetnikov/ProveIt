import FabiusFunction.NegativeLaplace

/-!
# Regularity of the negative-Laplace periodic correction

This file proves continuity of the exact periodic correction constructed in
`FabiusFunction.NegativeLaplace`.  The two infinite sums are treated uniformly
on one-sided positive intervals.  The small-scale logarithmic product has a
geometric `2⁻ⁿ` majorant on `(0, b]`, while the forward tail has a geometric
majorant with ratio `exp (-a)` on `[a, ∞)` for `a > 0`.

The resulting global continuity statements, together with the imported
one-periodicity of the exact correction and its transfer to the centered
normalization, form the regularity interface used by the later mean, Fourier,
and derivative modules.  We also record interval integrability on arbitrary
finite intervals and the exact decomposition of the correction into its
centered part and its mean.
-/

set_option autoImplicit false

open scoped BigOperators
open Set Filter Topology

namespace Fabius

/-- Each small-scale term is continuous on the positive half-line. -/
theorem continuousOn_negativeLaplaceTerm (n : ℕ) :
    ContinuousOn (fun s : ℝ => negativeLaplaceTerm s n) (Ioi 0) := by
  intro s hs
  change 0 < s at hs
  apply ContinuousAt.continuousWithinAt
  unfold negativeLaplaceTerm negativeLaplaceKernel
  have hden : s / (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  have hnum : 1 - Real.exp (-(s / (2 : ℝ) ^ (n + 1))) ≠ 0 := by
    apply (sub_pos.mpr ?_).ne'
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (by positivity))
  have hratio : (1 - Real.exp (-(s / (2 : ℝ) ^ (n + 1)))) /
      (s / (2 : ℝ) ^ (n + 1)) ≠ 0 := div_ne_zero hnum hden
  fun_prop (disch := assumption)

/-- The logarithmic product is continuous on every interval `(0, b]`.  Its
geometric majorant only needs the upper bound `s ≤ b`. -/
theorem continuousOn_negativeLaplaceLog_Ioc (b : ℝ) :
    ContinuousOn negativeLaplaceLog (Ioc 0 b) := by
  change ContinuousOn
    (fun s : ℝ => ∑' n : ℕ, negativeLaplaceTerm s n) _
  apply continuousOn_tsum
  · intro n
    exact (continuousOn_negativeLaplaceTerm n).mono
      (fun _ hs => hs.1)
  · exact summable_geometric_two' b
  · intro n s hs
    rw [Real.norm_eq_abs]
    refine (abs_negativeLaplaceTerm_le s hs.1 n).trans ?_
    gcongr
    exact hs.2

/-- Compatibility form on a compact positive interval. -/
theorem continuousOn_negativeLaplaceLog_Icc
    (a b : ℝ) (ha : 0 < a) :
    ContinuousOn negativeLaplaceLog (Icc a b) :=
  (continuousOn_negativeLaplaceLog_Ioc b).mono fun _ hs =>
    ⟨ha.trans_le hs.1, hs.2⟩

/-- The logarithmic product is continuous at every positive scale. -/
theorem continuousAt_negativeLaplaceLog (s : ℝ) (hs : 0 < s) :
    ContinuousAt negativeLaplaceLog s := by
  exact (continuousOn_negativeLaplaceLog_Icc
      (s / 2) (3 * s / 2) (by positivity)).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- The logarithmic product is continuous throughout the positive half-line. -/
theorem continuousOn_negativeLaplaceLog :
    ContinuousOn negativeLaplaceLog (Ioi 0) := by
  intro s hs
  exact (continuousAt_negativeLaplaceLog s hs).continuousWithinAt

/-- Each forward-tail term is continuous on the positive half-line. -/
theorem continuousOn_negativeLaplaceForwardTerm (n : ℕ) :
    ContinuousOn (fun s : ℝ => negativeLaplaceForwardTerm s n) (Ioi 0) := by
  intro s hs
  change 0 < s at hs
  apply ContinuousAt.continuousWithinAt
  unfold negativeLaplaceForwardTerm
  have hnum : 1 - Real.exp (-(s * (2 : ℝ) ^ n)) ≠ 0 := by
    apply (sub_pos.mpr ?_).ne'
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (by positivity))
  fun_prop (disch := assumption)

/-- The forward tail is continuous on every closed positive half-line
`[a, ∞)`.  Its summable majorant only uses the lower bound `a ≤ s`. -/
theorem continuousOn_negativeLaplaceForwardTail_Ici
    (a : ℝ) (ha : 0 < a) :
    ContinuousOn negativeLaplaceForwardTail (Ici a) := by
  let r := Real.exp (-a)
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hmajor : Summable (fun n : ℕ => r ^ (n + 1) / (1 - r)) := by
    have hgeom : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hr0 hr1
    refine (hgeom.mul_left (r / (1 - r))).congr ?_
    intro n
    rw [pow_succ']
    ring
  change ContinuousOn
    (fun s : ℝ => ∑' n : ℕ, negativeLaplaceForwardTerm s n) _
  apply continuousOn_tsum
  · intro n
    exact (continuousOn_negativeLaplaceForwardTerm n).mono
      (fun _ hs => ha.trans_le hs)
  · exact hmajor
  · intro n s hs
    rw [Real.norm_eq_abs]
    refine (abs_negativeLaplaceForwardTerm_le s
      (ha.trans_le hs) n).trans ?_
    have hexp : Real.exp (-s) ≤ r := by
      change Real.exp (-s) ≤ Real.exp (-a)
      apply Real.exp_le_exp.mpr
      exact neg_le_neg hs
    have hnum : Real.exp (-s) ^ (n + 1) ≤ r ^ (n + 1) :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hexp _
    have hden : 0 < 1 - r := sub_pos.mpr hr1
    have hden' : 1 - r ≤ 1 - Real.exp (-s) := sub_le_sub_left hexp 1
    exact (div_le_div_of_nonneg_left
      (pow_nonneg (Real.exp_nonneg _) _) hden hden').trans
        (div_le_div_of_nonneg_right hnum hden.le)

/-- Compatibility form on a compact positive interval. -/
theorem continuousOn_negativeLaplaceForwardTail_Icc
    (a b : ℝ) (ha : 0 < a) :
    ContinuousOn negativeLaplaceForwardTail (Icc a b) :=
  (continuousOn_negativeLaplaceForwardTail_Ici a ha).mono fun _ hs => hs.1

/-- The forward tail is continuous at every positive scale. -/
theorem continuousAt_negativeLaplaceForwardTail (s : ℝ) (hs : 0 < s) :
    ContinuousAt negativeLaplaceForwardTail s := by
  exact (continuousOn_negativeLaplaceForwardTail_Icc
      (s / 2) (3 * s / 2) (by positivity)).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- The forward tail is continuous throughout the positive half-line. -/
theorem continuousOn_negativeLaplaceForwardTail :
    ContinuousOn negativeLaplaceForwardTail (Ioi 0) := by
  intro s hs
  exact (continuousAt_negativeLaplaceForwardTail s hs).continuousWithinAt

/-- The multiplicatively periodic correction is continuous at positive scales. -/
theorem continuousAt_negativeLaplaceMultiplicativeCorrection
    (s : ℝ) (hs : 0 < s) :
    ContinuousAt negativeLaplaceMultiplicativeCorrection s := by
  unfold negativeLaplaceMultiplicativeCorrection
  dsimp only
  have ht : ContinuousAt (fun u : ℝ => Real.logb 2 u) s := by
    unfold Real.logb
    fun_prop (disch := positivity)
  exact ((continuousAt_negativeLaplaceLog s hs).add
    (continuousAt_const.mul ((ht.pow 2).sub ht))).add
      (continuousAt_negativeLaplaceForwardTail s hs)

/-- The multiplicative correction is continuous throughout the positive
half-line. -/
theorem continuousOn_negativeLaplaceMultiplicativeCorrection :
    ContinuousOn negativeLaplaceMultiplicativeCorrection (Ioi 0) := by
  intro s hs
  exact (continuousAt_negativeLaplaceMultiplicativeCorrection s hs).continuousWithinAt

/-- The exact one-periodic logarithmic correction is continuous. -/
theorem continuous_negativeLaplacePeriodicCorrection :
    Continuous negativeLaplacePeriodicCorrection := by
  rw [continuous_iff_continuousAt]
  intro t
  unfold negativeLaplacePeriodicCorrection
  change ContinuousAt
    (negativeLaplaceMultiplicativeCorrection ∘ fun u : ℝ => (2 : ℝ) ^ u) t
  apply ContinuousAt.comp
  · exact continuousAt_negativeLaplaceMultiplicativeCorrection _
      (Real.rpow_pos_of_pos (by norm_num) _)
  · exact (Real.continuous_const_rpow
      (by norm_num : (2 : ℝ) ≠ 0)).continuousAt

/-- The exact periodic correction is interval integrable on every finite
real interval. -/
theorem intervalIntegrable_negativeLaplacePeriodicCorrection (a b : ℝ) :
    IntervalIntegrable negativeLaplacePeriodicCorrection
      MeasureTheory.volume a b :=
  continuous_negativeLaplacePeriodicCorrection.intervalIntegrable a b

/-- The mean of the exact periodic correction over one period. -/
noncomputable def negativeLaplacePeriodicMean : ℝ :=
  ∫ t in (0 : ℝ)..1, negativeLaplacePeriodicCorrection t

/-- The zero-mean normalization of the exact periodic correction. -/
noncomputable def negativeLaplacePsi (t : ℝ) : ℝ :=
  negativeLaplacePeriodicCorrection t - negativeLaplacePeriodicMean

/-- The normalized periodic correction remains continuous. -/
theorem continuous_negativeLaplacePsi : Continuous negativeLaplacePsi := by
  exact continuous_negativeLaplacePeriodicCorrection.sub continuous_const

/-- The centered correction is interval integrable on every finite real
interval. -/
theorem intervalIntegrable_negativeLaplacePsi (a b : ℝ) :
    IntervalIntegrable negativeLaplacePsi MeasureTheory.volume a b :=
  continuous_negativeLaplacePsi.intervalIntegrable a b

/-- Reconstructing the exact correction from its centered normalization and
its mean. -/
theorem negativeLaplacePeriodicCorrection_eq_negativeLaplacePsi_add_mean
    (t : ℝ) :
    negativeLaplacePeriodicCorrection t =
      negativeLaplacePsi t + negativeLaplacePeriodicMean := by
  rw [negativeLaplacePsi]
  ring

/-- The normalized correction is one-periodic. -/
theorem negativeLaplacePsi_add_one (t : ℝ) :
    negativeLaplacePsi (t + 1) = negativeLaplacePsi t := by
  rw [negativeLaplacePsi, negativeLaplacePsi,
    negativeLaplacePeriodicCorrection_add_one]

/-- The normalized correction has integral zero over its defining period. -/
theorem integral_negativeLaplacePsi_zero :
    (∫ t in (0 : ℝ)..1, negativeLaplacePsi t) = 0 := by
  simp_rw [negativeLaplacePsi]
  have hR : IntervalIntegrable negativeLaplacePeriodicCorrection
      MeasureTheory.volume 0 1 :=
    intervalIntegrable_negativeLaplacePeriodicCorrection 0 1
  have hc : IntervalIntegrable (fun _ : ℝ => negativeLaplacePeriodicMean)
      MeasureTheory.volume 0 1 := intervalIntegrable_const
  rw [intervalIntegral.integral_sub hR hc]
  rw [intervalIntegral.integral_const]
  simp [negativeLaplacePeriodicMean]

end Fabius
