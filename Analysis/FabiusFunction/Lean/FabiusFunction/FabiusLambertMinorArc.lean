import FabiusFunction.FabiusLambertSaddle
import FabiusFunction.NegativeLaplaceMinorArc
import FabiusFunction.FabiusSaddleTail

/-!
# Minor-arc extraction along the explicit dyadic Lambert saddle

The Lambert phase `lambda(t)` is the natural first-order variance scale of
the Fabius saddle at `x = 2⁻ᵗ`.  We extract

`m(t) = ceil (lambda(t) / 4)`

pairs of dyadic factors.  Thus `2m(t) = lambda(t)/2 + O(1)`, which is exactly
the factor count required by the complementary-tail estimate.  At this
count, even the last extracted argument tends exponentially to infinity, so
the finite coth product is uniformly bounded by `exp 4`.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped Topology

namespace Fabius

/-- Number of factor pairs extracted at the dyadic Lambert saddle. -/
noncomputable def dyadicLambertExtractionCount (t : ℝ) : ℕ :=
  ⌈dyadicLambertPhase t / 4⌉₊

/-- The extraction count dominates one quarter of the Lambert variance scale. -/
lemma dyadicLambertPhase_div_four_le_extractionCount (t : ℝ) :
    dyadicLambertPhase t / 4 ≤ (dyadicLambertExtractionCount t : ℝ) := by
  exact Nat.le_ceil _

/-- The ceiling costs less than one extra factor pair once the phase is nonnegative. -/
lemma dyadicLambertExtractionCount_lt_phase_div_four_add_one
    {t : ℝ} (ht : 0 ≤ dyadicLambertPhase t) :
    (dyadicLambertExtractionCount t : ℝ) < dyadicLambertPhase t / 4 + 1 := by
  exact Nat.ceil_lt_add_one (by positivity)

/-- Consequently `2m` lies within two of one half of the Lambert scale. -/
lemma dyadicLambertExtractionCount_two_mul_bounds
    {t : ℝ} (ht : 0 ≤ dyadicLambertPhase t) :
    dyadicLambertPhase t / 2 ≤
        (2 * dyadicLambertExtractionCount t : ℕ) ∧
      ((2 * dyadicLambertExtractionCount t : ℕ) : ℝ) <
        dyadicLambertPhase t / 2 + 2 := by
  constructor
  · have h := dyadicLambertPhase_div_four_le_extractionCount t
    push_cast
    linarith
  · have h := dyadicLambertExtractionCount_lt_phase_div_four_add_one ht
    push_cast
    linarith

/-- The number of extracted factor pairs tends to infinity. -/
theorem tendsto_dyadicLambertExtractionCount_atTop :
    Tendsto dyadicLambertExtractionCount atTop atTop := by
  unfold dyadicLambertExtractionCount
  exact tendsto_nat_ceil_atTop.comp
    (tendsto_dyadicLambertPhase_atTop.atTop_div_const (by norm_num))

/-- Eventually at least one factor pair is extracted. -/
theorem eventually_one_le_dyadicLambertExtractionCount :
    ∀ᶠ t : ℝ in atTop, 1 ≤ dyadicLambertExtractionCount t :=
  tendsto_dyadicLambertExtractionCount_atTop.eventually_ge_atTop 1

/-- Eventually the elementary geometric-tail inequality `m² ≤ 2ᵐ` holds. -/
theorem eventually_dyadicLambertExtractionCount_sq_le_two_pow :
    ∀ᶠ t : ℝ in atTop,
      (dyadicLambertExtractionCount t : ℝ) ^ 2 ≤
        (2 : ℝ) ^ dyadicLambertExtractionCount t := by
  filter_upwards
    [tendsto_dyadicLambertExtractionCount_atTop.eventually_ge_atTop 4] with t ht
  exact natCast_sq_le_two_pow ht

private lemma dyadicLambert_linear_exp_decay (c : ℝ) (hc : 0 < c) :
    Tendsto
      (fun t : ℝ =>
        dyadicLambertPhase t * Real.exp (-c * dyadicLambertPhase t))
      atTop (𝓝 0) := by
  convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp
      tendsto_dyadicLambertPhase_atTop using 1
  simp [Function.comp_def]

private lemma eventually_dyadicLambert_minorArc_arguments :
    ∀ᶠ t : ℝ in atTop, ∀ n < 2 * dyadicLambertExtractionCount t,
      dyadicLambertPhase t / 8 ≤
        fabiusLambertRadius ((2 : ℝ) ^ (-t)) / (2 : ℝ) ^ (n + 1) := by
  have hdecay := dyadicLambert_linear_exp_decay
    (Real.log 2 / 2) (by positivity)
  have hdecayOne : ∀ᶠ t : ℝ in atTop,
      dyadicLambertPhase t *
          Real.exp (-(Real.log 2 / 2) * dyadicLambertPhase t) ≤ 1 :=
    hdecay.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards
    [tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 4, hdecayOne]
      with t hphase hdecayAt n hn
  have hcountUpper :=
    dyadicLambertExtractionCount_lt_phase_div_four_add_one
      (by linarith : 0 ≤ dyadicLambertPhase t)
  have hnCast : ((n + 1 : ℕ) : ℝ) ≤ dyadicLambertPhase t / 2 + 2 := by
    have hnNat : n + 1 ≤ 2 * dyadicLambertExtractionCount t := by omega
    calc
      ((n + 1 : ℕ) : ℝ) ≤
          ((2 * dyadicLambertExtractionCount t : ℕ) : ℝ) := by exact_mod_cast hnNat
      _ = 2 * (dyadicLambertExtractionCount t : ℝ) := by norm_num
      _ ≤ 2 * (dyadicLambertPhase t / 4 + 1) := by linarith
      _ = dyadicLambertPhase t / 2 + 2 := by ring
  have hphaseExp : dyadicLambertPhase t ≤
      Real.exp ((Real.log 2 / 2) * dyadicLambertPhase t) := by
    have hexp : 0 < Real.exp ((Real.log 2 / 2) * dyadicLambertPhase t) :=
      Real.exp_pos _
    rw [show Real.exp (-(Real.log 2 / 2) * dyadicLambertPhase t) =
        (Real.exp ((Real.log 2 / 2) * dyadicLambertPhase t))⁻¹ by
          rw [← Real.exp_neg]
          congr 1
          ring] at hdecayAt
    exact (div_le_one hexp).mp (by simpa [div_eq_mul_inv] using hdecayAt)
  have hbase : dyadicLambertPhase t / 8 ≤
      (2 : ℝ) ^ (dyadicLambertPhase t / 2 - 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      calc
        Real.log (4 : ℝ) = Real.log ((2 : ℝ) * 2) := by norm_num
        _ = Real.log 2 + Real.log 2 := by
          rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
        _ = 2 * Real.log 2 := by ring
    have hrewrite :
        Real.exp (Real.log 2 * (dyadicLambertPhase t / 2 - 2)) =
          Real.exp ((Real.log 2 / 2) * dyadicLambertPhase t) / 4 := by
      have hexponent : Real.log 2 * (dyadicLambertPhase t / 2 - 2) =
          (Real.log 2 / 2) * dyadicLambertPhase t - Real.log 4 := by
        rw [hlogFour]
        ring
      rw [hexponent, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    rw [hrewrite]
    nlinarith [Real.exp_pos ((Real.log 2 / 2) * dyadicLambertPhase t)]
  calc
    dyadicLambertPhase t / 8 ≤
        (2 : ℝ) ^ (dyadicLambertPhase t / 2 - 2) := hbase
    _ ≤ (2 : ℝ) ^ (dyadicLambertPhase t - ((n + 1 : ℕ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    _ = fabiusLambertRadius ((2 : ℝ) ^ (-t)) / (2 : ℝ) ^ (n + 1) := by
      rw [fabiusLambertRadius_dyadic, Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
        Real.rpow_natCast]

private lemma eventually_dyadicLambert_minorArc_count :
    ∀ᶠ t : ℝ in atTop,
      ((2 * dyadicLambertExtractionCount t : ℕ) : ℝ) *
          Real.exp (-(dyadicLambertPhase t / 8)) ≤ 1 := by
  have hdecay := dyadicLambert_linear_exp_decay (1 / 8) (by norm_num)
  have hdecayOne : ∀ᶠ t : ℝ in atTop,
      dyadicLambertPhase t * Real.exp (-(1 / 8) * dyadicLambertPhase t) ≤ 1 :=
    hdecay.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards
    [tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop 4, hdecayOne]
      with t hphase hdecayAt
  have hcountUpper :=
    dyadicLambertExtractionCount_lt_phase_div_four_add_one
      (by linarith : 0 ≤ dyadicLambertPhase t)
  have hcount : ((2 * dyadicLambertExtractionCount t : ℕ) : ℝ) ≤
      dyadicLambertPhase t := by
    push_cast
    linarith
  calc
    ((2 * dyadicLambertExtractionCount t : ℕ) : ℝ) *
        Real.exp (-(dyadicLambertPhase t / 8)) ≤
      dyadicLambertPhase t * Real.exp (-(dyadicLambertPhase t / 8)) := by
        gcongr
    _ = dyadicLambertPhase t *
        Real.exp (-(1 / 8) * dyadicLambertPhase t) := by ring_nf
    _ ≤ 1 := hdecayAt

/-- The finite minor-arc product at the explicit dyadic Lambert radius and
the natural extraction count is eventually at most `exp 4`. -/
theorem eventually_negativeLaplaceMinorArcConstant_dyadicLambert_le_exp_four :
    ∀ᶠ t : ℝ in atTop,
      negativeLaplaceMinorArcConstant
          (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
          (2 * dyadicLambertExtractionCount t) ≤ Real.exp 4 := by
  filter_upwards
    [tendsto_dyadicLambertPhase_atTop.eventually_ge_atTop (8 * Real.log 2),
      eventually_dyadicLambert_minorArc_arguments,
      eventually_dyadicLambert_minorArc_count]
      with t hphase harg hcount
  apply negativeLaplaceMinorArcConstant_le_exp_four
      (b := dyadicLambertPhase t / 8)
  · linarith
  · exact harg
  · simpa only [neg_div] using hcount

/-- Uniform `O(1)` form consumed by the complementary Fabius saddle-tail theorem. -/
theorem negativeLaplaceMinorArcConstant_dyadicLambert_isBigO :
    (fun t : ℝ =>
      negativeLaplaceMinorArcConstant
        (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
        (2 * dyadicLambertExtractionCount t)) =O[atTop]
      (fun _t : ℝ => (1 : ℝ)) := by
  apply IsBigO.of_bound (Real.exp 4)
  filter_upwards
    [eventually_negativeLaplaceMinorArcConstant_dyadicLambert_le_exp_four]
      with t ht
  have hpos := negativeLaplaceMinorArcConstant_pos
    (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
    (fabiusLambertRadius_pos _) (2 * dyadicLambertExtractionCount t)
  simpa [Real.norm_eq_abs, abs_of_pos hpos] using ht

/-- The complementary normalized saddle tail is `O(1 / lambda(t))` at the
explicit dyadic Lambert radius, with no remaining minor-arc hypothesis. -/
theorem integral_norm_fabius_scaledSaddleKernel_dyadicLambert_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun t : ℝ => ∫ v in
      (Set.Icc (-fabiusSaddleCentralRadius (dyadicLambertPhase t))
        (fabiusSaddleCentralRadius (dyadicLambertPhase t)))ᶜ,
      ‖QuantitativeSaddle.scaledSaddleKernel
        (fun z => complexGeneratingFunction F (-z))
          ((2 : ℝ) ^ (-t))
          (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
          (dyadicLambertPhase t) v‖) =O[atTop]
      (fun t : ℝ => (dyadicLambertPhase t)⁻¹) := by
  apply integral_norm_fabius_scaledSaddleKernel_standardRadius_isBigO
    atTop F hF
    (fun t : ℝ => (2 : ℝ) ^ (-t))
    (fun t : ℝ => fabiusLambertRadius ((2 : ℝ) ^ (-t)))
    dyadicLambertPhase dyadicLambertExtractionCount
  · exact Filter.Eventually.of_forall fun t => fabiusLambertRadius_pos _
  · exact tendsto_dyadicLambertPhase_atTop
  · exact Filter.Eventually.of_forall
      dyadicLambertPhase_div_four_le_extractionCount
  · exact negativeLaplaceMinorArcConstant_dyadicLambert_isBigO

end Fabius
