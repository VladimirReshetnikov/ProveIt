import FabiusFunction.FabiusSaddleCentralLambert
import FabiusFunction.FabiusExplicitSharpTransfer
import FabiusFunction.FabiusWikipediaObstruction
import FabiusFunction.FabiusDyadicSharpAsymptotic
import FabiusFunction.PeriodicFourier
import FabiusFunction.FabiusQuotientExponentialMismatch
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Ultrafilter

/-!
# Sharp small-argument asymptotics of the Fabius function

This module closes the quantitative saddle argument and exposes its
source-facing consequences.  The elementary expression printed in the linked
Math Stack Exchange discussion is missing a genuine nonconstant periodic
term.  Adding `negativeLaplacePsi` at the exact lower-Lambert phase gives an
`O(1 / (-log x))` error; deleting it does not even preserve asymptotic
equivalence after exponentiation.

The related quotient-of-exponentials approximation is imported here as well.
It is a useful numerical fit on a compact interval, but its endpoint decay is
strictly faster than the Fabius bump and hence it is not an asymptotic
equivalent.  Both the compact Lambert expression and its literal logarithmic
expansion are exposed as vanishing log errors and as exponentiated asymptotic
equivalents; a generic log-to-exponential transfer lemma factors their common
proof.
-/

set_option autoImplicit false

open Filter Set Asymptotics

namespace Fabius

/-- Exponentiating an asymptotically vanishing logarithmic error produces an
asymptotic equivalent.  Eventual positivity is the only hypothesis needed to
recover the original function from its logarithm. -/
theorem isEquivalent_exp_of_tendsto_log_sub
    {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf : ∀ᶠ x in l, 0 < f x)
    (hlog : Tendsto (fun x => Real.log (f x) - g x) l (nhds 0)) :
    f ~[l] fun x => Real.exp (g x) := by
  have hexp : Tendsto
      (fun x => Real.exp (Real.log (f x) - g x)) l (nhds 1) := by
    convert Real.continuous_exp.continuousAt.tendsto.comp hlog using 1
    · rfl
    · simp
  apply isEquivalent_of_tendsto_one
  apply hexp.congr'
  filter_upwards [hf] with x hx
  rw [Real.exp_sub, Real.exp_log hx]
  rfl

/-- For an eventually positive real function, asymptotic equivalence to an
exponential is equivalent to convergence of the corresponding logarithmic
error to zero. -/
theorem isEquivalent_exp_iff_tendsto_log_sub
    {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf : ∀ᶠ x in l, 0 < f x) :
    f ~[l] (fun x => Real.exp (g x)) ↔
      Tendsto (fun x => Real.log (f x) - g x) l (nhds 0) := by
  constructor
  · intro hequiv
    have hratio :
        Tendsto (fun x => f x / Real.exp (g x)) l (nhds 1) :=
      (isEquivalent_iff_tendsto_one
        (Eventually.of_forall fun x : α => Real.exp_ne_zero (g x))).mp hequiv
    have hlogRatio :
        Tendsto (fun x => Real.log (f x / Real.exp (g x))) l (nhds 0) := by
      simpa using hratio.log one_ne_zero
    apply hlogRatio.congr'
    filter_upwards [hf] with x hx
    rw [Real.log_div hx.ne' (Real.exp_ne_zero _), Real.log_exp]
  · intro hlog
    exact isEquivalent_exp_of_tendsto_log_sub hf hlog

/-- The reciprocal logarithmic error scale tends to zero at the positive
endpoint. -/
theorem tendsto_inv_neg_log_nhdsGT_zero :
    Tendsto (fun x : ℝ => (-Real.log x)⁻¹)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_inv_atTop_zero.comp
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)

/-- Unconditional compact Lambert-coordinate form of the corrected sharp
small-argument asymptotic. -/
theorem log_fabius_sub_correctedWikipediaMain_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun x : ℝ => Real.log (fabiusReal F x) -
        fabiusCorrectedWikipediaMain x) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => (-Real.log x)⁻¹) :=
  log_fabius_sub_correctedWikipediaMain_isBigO_of_kernelMass F hF
    (SaddleLambert.fabiusSaddleKernelMass_dyadicLambert_sub_one_isBigO F hF)

/-- Unconditional literal `log x`/`log (-log x)` expansion, corrected by the
nonconstant periodic term at the exact lower-Lambert phase. -/
theorem log_fabius_sub_explicitCorrectedWikipediaMain_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun x : ℝ => Real.log (fabiusReal F x) -
        fabiusExplicitCorrectedWikipediaMain x) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => (-Real.log x)⁻¹) :=
  log_fabius_sub_explicitCorrectedWikipediaMain_isBigO_of_kernelMass F hF
    (SaddleLambert.fabiusSaddleKernelMass_dyadicLambert_sub_one_isBigO F hF)

/-- The compact Lambert-coordinate logarithmic error tends to zero. -/
theorem tendsto_log_fabius_sub_correctedWikipediaMain
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto
      (fun x : ℝ => Real.log (fabiusReal F x) -
        fabiusCorrectedWikipediaMain x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  (log_fabius_sub_correctedWikipediaMain_isBigO F hF).trans_tendsto
    tendsto_inv_neg_log_nhdsGT_zero

/-- The logarithmic residual of the exact compact online Lambert expression
does not tend to zero: its nonvanishing part is the centered periodic
correction sampled at the exact lower-Lambert phase. -/
theorem log_fabius_sub_WikipediaLambertMain_not_tendsto_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ Tendsto
      (fun x : ℝ => Real.log (fabiusReal F x) -
        fabiusWikipediaLambertMain x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  intro huncorrected
  apply negativeLaplacePsi_comp_fabiusLambertPhase_not_tendsto_zero
  have hdiff := huncorrected.sub
    (tendsto_log_fabius_sub_correctedWikipediaMain F hF)
  simpa only [sub_zero] using hdiff.congr'
    (Eventually.of_forall fun x => by
      rw [fabiusCorrectedWikipediaMain_eq_WikipediaLambertMain_add]
      simp only [Function.comp_apply]
      ring)

/-- The logarithmic residual of the exact compact online Lambert expression
is not `O(1 / (-log x))` at the positive endpoint. -/
theorem log_fabius_sub_WikipediaLambertMain_not_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ ((fun x : ℝ => Real.log (fabiusReal F x) -
          fabiusWikipediaLambertMain x) =O[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => (-Real.log x)⁻¹)) := by
  intro hO
  exact log_fabius_sub_WikipediaLambertMain_not_tendsto_zero F hF
    (hO.trans_tendsto tendsto_inv_neg_log_nhdsGT_zero)

/-- The literal logarithmic error tends to zero. -/
theorem tendsto_log_fabius_sub_explicitCorrectedWikipediaMain
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto
      (fun x : ℝ => Real.log (fabiusReal F x) -
        fabiusExplicitCorrectedWikipediaMain x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  (log_fabius_sub_explicitCorrectedWikipediaMain_isBigO F hF).trans_tendsto
    tendsto_inv_neg_log_nhdsGT_zero

/-- The same `O(1 / (-log x))` claim is false for the uncorrected elementary
formula because its omitted periodic correction is nonzero. -/
theorem log_fabius_sub_WikipediaElementaryMain_not_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ ((fun x : ℝ => Real.log (fabiusReal F x) -
          fabiusWikipediaElementaryMain x) =O[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => (-Real.log x)⁻¹)) :=
  log_fabius_sub_WikipediaElementaryMain_not_isBigO_of_kernelMass F hF
    (SaddleLambert.fabiusSaddleKernelMass_dyadicLambert_sub_one_isBigO F hF)

/-- Exponentiating the compact corrected logarithmic formula gives the same
asymptotic equivalent as its literal expansion. -/
theorem fabius_isEquivalent_exp_correctedWikipediaMain
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun x : ℝ => fabiusReal F x) ~[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => Real.exp (fabiusCorrectedWikipediaMain x)) := by
  apply isEquivalent_exp_of_tendsto_log_sub
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact fabius_pos_of_pos F hF hx
  · exact tendsto_log_fabius_sub_correctedWikipediaMain F hF

/-- The exponential of the exact compact nonperiodic Lambert expression
printed online is not asymptotically equivalent to a bounded Fabius solution. -/
theorem fabius_not_isEquivalent_exp_WikipediaLambertMain
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ ((fun x : ℝ => fabiusReal F x) ~[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => Real.exp (fabiusWikipediaLambertMain x))) := by
  intro hequiv
  apply log_fabius_sub_WikipediaLambertMain_not_tendsto_zero F hF
  have hpositive :
      ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0), 0 < fabiusReal F x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fabius_pos_of_pos F hF hx
  exact (isEquivalent_exp_iff_tendsto_log_sub hpositive).mp hequiv

/-- Exponentiating the corrected logarithmic formula gives the asymptotic
equivalent requested in the linked Math Stack Exchange question. -/
theorem fabius_isEquivalent_exp_explicitCorrectedWikipediaMain
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun x : ℝ => fabiusReal F x) ~[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => Real.exp (fabiusExplicitCorrectedWikipediaMain x)) := by
  apply isEquivalent_exp_of_tendsto_log_sub
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact fabius_pos_of_pos F hF hx
  · exact tendsto_log_fabius_sub_explicitCorrectedWikipediaMain F hF

/-- The exponential of the literal uncorrected Wikipedia logarithmic
expression is not an asymptotic equivalent of the Fabius function. -/
theorem fabius_not_isEquivalent_exp_WikipediaElementaryMain
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ ((fun x : ℝ => fabiusReal F x) ~[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => Real.exp (fabiusWikipediaElementaryMain x))) := by
  intro hequiv
  apply negativeLaplacePsi_comp_fabiusLambertPhase_not_tendsto_zero
  have hratio :
      Tendsto
        (fun x : ℝ => fabiusReal F x /
          Real.exp (fabiusWikipediaElementaryMain x))
        (nhdsWithin 0 (Ioi 0)) (nhds 1) :=
    (isEquivalent_iff_tendsto_one
      (Eventually.of_forall fun x : ℝ =>
        Real.exp_ne_zero (fabiusWikipediaElementaryMain x))).mp hequiv
  have hlogRatio :
      Tendsto
        (fun x : ℝ => Real.log (fabiusReal F x /
          Real.exp (fabiusWikipediaElementaryMain x)))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using hratio.log one_ne_zero
  have huncorrected :
      Tendsto
        (fun x : ℝ => Real.log (fabiusReal F x) -
          fabiusWikipediaElementaryMain x)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    apply hlogRatio.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.log_div (fabius_pos_of_pos F hF hx).ne'
      (Real.exp_ne_zero _), Real.log_exp]
  have hdiff := huncorrected.sub
    (tendsto_log_fabius_sub_explicitCorrectedWikipediaMain F hF)
  simpa only [sub_zero] using hdiff.congr' (Eventually.of_forall fun x => by
    simp only [fabiusExplicitCorrectedWikipediaMain, Function.comp_apply]
    ring)

/-! ## The literal online factor and its exact oscillatory quotient -/

/-- The corrected sharp asymptotic can be written directly with the literal
multiplicative factor printed in the online source.  The missing factor is the
exponential of the centered periodic correction at the exact Lambert phase. -/
theorem fabius_isEquivalent_WikipediaLambertFactor_mul_periodic
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun x : ℝ => fabiusReal F x) ~[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => fabiusWikipediaLambertFactor x *
        Real.exp (negativeLaplacePsi (fabiusLambertPhase x))) := by
  refine (fabius_isEquivalent_exp_correctedWikipediaMain F hF).congr_right ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact
    exp_fabiusCorrectedWikipediaMain_eq_WikipediaLambertFactor_mul_periodic hx

/-- The least value of the centered negative-Laplace correction on one closed
period.  Periodicity makes this the global minimum as well. -/
noncomputable def negativeLaplacePsiPeriodMin : ℝ :=
  sInf (negativeLaplacePsi '' Icc (0 : ℝ) 1)

/-- The greatest value of the centered negative-Laplace correction on one
closed period.  Periodicity makes this the global maximum as well. -/
noncomputable def negativeLaplacePsiPeriodMax : ℝ :=
  sSup (negativeLaplacePsi '' Icc (0 : ℝ) 1)

private theorem image_Icc_negativeLaplacePsi_eq_periodExtrema :
    negativeLaplacePsi '' Icc (0 : ℝ) 1 =
      Icc negativeLaplacePsiPeriodMin negativeLaplacePsiPeriodMax := by
  simpa only [negativeLaplacePsiPeriodMin, negativeLaplacePsiPeriodMax] using
    continuous_negativeLaplacePsi.continuousOn.image_Icc
      (by norm_num : (0 : ℝ) ≤ 1)

/-- The global range of the centered periodic correction is exactly the
closed interval between its extrema on one period. -/
theorem range_negativeLaplacePsi_eq_Icc_periodMin_periodMax :
    range negativeLaplacePsi =
      Icc negativeLaplacePsiPeriodMin negativeLaplacePsiPeriodMax := by
  rw [← negativeLaplacePsi_periodic.image_Icc one_pos 0]
  simpa only [zero_add] using image_Icc_negativeLaplacePsi_eq_periodExtrema

/-- The period minimum is no larger than any value of the correction. -/
theorem negativeLaplacePsiPeriodMin_le_value (t : ℝ) :
    negativeLaplacePsiPeriodMin ≤ negativeLaplacePsi t := by
  have ht : negativeLaplacePsi t ∈ range negativeLaplacePsi := ⟨t, rfl⟩
  rw [range_negativeLaplacePsi_eq_Icc_periodMin_periodMax] at ht
  exact ht.1

/-- Every value of the correction is no larger than the period maximum. -/
theorem negativeLaplacePsi_value_le_periodMax (t : ℝ) :
    negativeLaplacePsi t ≤ negativeLaplacePsiPeriodMax := by
  have ht : negativeLaplacePsi t ∈ range negativeLaplacePsi := ⟨t, rfl⟩
  rw [range_negativeLaplacePsi_eq_Icc_periodMin_periodMax] at ht
  exact ht.2

/-- The minimum endpoint lies below the maximum endpoint. -/
theorem negativeLaplacePsiPeriodMin_le_periodMax :
    negativeLaplacePsiPeriodMin ≤ negativeLaplacePsiPeriodMax :=
  (negativeLaplacePsiPeriodMin_le_value 0).trans
    (negativeLaplacePsi_value_le_periodMax 0)

/-- The period minimum is attained on the canonical interval `[0, 1]`. -/
theorem exists_mem_Icc_negativeLaplacePsi_eq_periodMin :
    ∃ t ∈ Icc (0 : ℝ) 1,
      negativeLaplacePsi t = negativeLaplacePsiPeriodMin := by
  have hmin : negativeLaplacePsiPeriodMin ∈
      negativeLaplacePsi '' Icc (0 : ℝ) 1 := by
    rw [image_Icc_negativeLaplacePsi_eq_periodExtrema]
    exact left_mem_Icc.mpr negativeLaplacePsiPeriodMin_le_periodMax
  exact hmin

/-- The period maximum is attained on the canonical interval `[0, 1]`. -/
theorem exists_mem_Icc_negativeLaplacePsi_eq_periodMax :
    ∃ t ∈ Icc (0 : ℝ) 1,
      negativeLaplacePsi t = negativeLaplacePsiPeriodMax := by
  have hmax : negativeLaplacePsiPeriodMax ∈
      negativeLaplacePsi '' Icc (0 : ℝ) 1 := by
    rw [image_Icc_negativeLaplacePsi_eq_periodExtrema]
    exact right_mem_Icc.mpr negativeLaplacePsiPeriodMin_le_periodMax
  exact hmax

/-- The two extrema are distinct because the periodic correction is genuinely
nonconstant. -/
theorem negativeLaplacePsiPeriodMin_lt_periodMax :
    negativeLaplacePsiPeriodMin < negativeLaplacePsiPeriodMax := by
  refine lt_of_le_of_ne negativeLaplacePsiPeriodMin_le_periodMax ?_
  intro heq
  apply negativeLaplacePsi_not_constant
  refine ⟨negativeLaplacePsiPeriodMin, fun t => ?_⟩
  exact le_antisymm
    ((negativeLaplacePsi_value_le_periodMax t).trans_eq heq.symm)
    (negativeLaplacePsiPeriodMin_le_value t)

/-- Exponentiation transports the exact range interval of the correction to
the exact positive range interval of its multiplicative periodic factor. -/
theorem range_exp_negativeLaplacePsi_eq_Icc_periodExtrema :
    range (fun t : ℝ => Real.exp (negativeLaplacePsi t)) =
      Icc (Real.exp negativeLaplacePsiPeriodMin)
        (Real.exp negativeLaplacePsiPeriodMax) := by
  rw [Set.range_comp' Real.exp negativeLaplacePsi,
    range_negativeLaplacePsi_eq_Icc_periodMin_periodMax,
    Real.image_exp_Icc]

/-- The quotient of a bounded Fabius solution by the literal online Lambert
factor.  Its failure to converge is precisely the omitted periodic factor. -/
noncomputable def fabiusWikipediaLambertRatio
    (F : BoundedFabius) (x : ℝ) : ℝ :=
  fabiusReal F x / fabiusWikipediaLambertFactor x

/-- The literal-factor quotient is asymptotically equivalent to the exact
positive periodic factor sampled at the Lambert phase. -/
theorem fabiusWikipediaLambertRatio_isEquivalent_periodic
    (F : BoundedFabius) (hF : IsFabius F) :
    fabiusWikipediaLambertRatio F ~[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ =>
        Real.exp (negativeLaplacePsi (fabiusLambertPhase x))) := by
  have hquotient :
      fabiusWikipediaLambertRatio F ~[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ =>
          (fabiusWikipediaLambertFactor x *
              Real.exp (negativeLaplacePsi (fabiusLambertPhase x))) /
            fabiusWikipediaLambertFactor x) :=
    (fabius_isEquivalent_WikipediaLambertFactor_mul_periodic F hF).div
      (IsEquivalent.refl :
        (fun x : ℝ => fabiusWikipediaLambertFactor x)
          ~[nhdsWithin 0 (Ioi 0)]
            (fun x : ℝ => fabiusWikipediaLambertFactor x))
  refine hquotient.congr_right ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact mul_div_cancel_left₀ _ (fabiusWikipediaLambertFactor_pos hx).ne'

private theorem
    exp_negativeLaplacePsi_comp_fabiusLambertPhase_isBigO_one :
    (fun x : ℝ =>
        Real.exp (negativeLaplacePsi (fabiusLambertPhase x)))
      =O[nhdsWithin 0 (Ioi 0)] (fun _ : ℝ => (1 : ℝ)) := by
  apply IsBigO.of_bound (Real.exp negativeLaplacePsiPeriodMax)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one, mul_one]
  exact Real.exp_le_exp.mpr
    (negativeLaplacePsi_value_le_periodMax (fabiusLambertPhase x))

/-- More precisely than asymptotic equivalence, the literal-factor quotient
minus its periodic model tends additively to zero.  This is the form used to
transport the full cluster set. -/
theorem tendsto_fabiusWikipediaLambertRatio_sub_periodic
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto
      (fun x : ℝ => fabiusWikipediaLambertRatio F x -
        Real.exp (negativeLaplacePsi (fabiusLambertPhase x)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rw [← isLittleO_one_iff ℝ]
  exact
    (fabiusWikipediaLambertRatio_isEquivalent_periodic F hF).isLittleO.trans_isBigO
      exp_negativeLaplacePsi_comp_fabiusLambertPhase_isBigO_one

private theorem mapClusterPt_iff_of_tendsto_sub_zero
    {a : Type*} {l : Filter a} {f g : a → ℝ} {z : ℝ}
    (h : Tendsto (fun x => f x - g x) l (nhds 0)) :
    MapClusterPt z l f ↔ MapClusterPt z l g := by
  have hdist : Tendsto (fun x => dist (f x) (g x)) l (nhds 0) := by
    simpa only [Real.dist_eq, abs_zero] using h.abs
  constructor
  · intro hf
    rw [mapClusterPt_iff_ultrafilter] at hf ⊢
    rcases hf with ⟨U, hU, hfU⟩
    exact ⟨U, hU, hfU.congr_dist (hdist.mono_left hU)⟩
  · intro hg
    rw [mapClusterPt_iff_ultrafilter] at hg ⊢
    rcases hg with ⟨U, hU, hgU⟩
    refine ⟨U, hU, hgU.congr_dist ?_⟩
    exact (hdist.mono_left hU).congr'
      (Eventually.of_forall fun x => dist_comm (f x) (g x))

/-- The cluster values of the literal-factor quotient at `x → 0⁺` are
exactly the closed interval swept out by the omitted positive periodic factor.
Thus the compact expression does not merely miss a constant normalization: it
misses a continuum of limiting quotient values. -/
theorem mapClusterPt_fabiusWikipediaLambertRatio_nhdsGT_zero_iff
    (F : BoundedFabius) (hF : IsFabius F) {z : ℝ} :
    MapClusterPt z (nhdsWithin 0 (Ioi 0))
        (fabiusWikipediaLambertRatio F) ↔
      z ∈ Icc (Real.exp negativeLaplacePsiPeriodMin)
        (Real.exp negativeLaplacePsiPeriodMax) := by
  have hperiodic :
      Function.Periodic
        (fun t : ℝ => Real.exp (negativeLaplacePsi t)) 1 := by
    simpa only [Function.comp_def] using
      negativeLaplacePsi_periodic.comp Real.exp
  have hcontinuous :
      Continuous (fun t : ℝ => Real.exp (negativeLaplacePsi t)) := by
    simpa only [Function.comp_def] using
      Real.continuous_exp.comp continuous_negativeLaplacePsi
  calc
    MapClusterPt z (nhdsWithin 0 (Ioi 0))
        (fabiusWikipediaLambertRatio F) ↔
        MapClusterPt z (nhdsWithin 0 (Ioi 0))
          (fun x : ℝ =>
            Real.exp (negativeLaplacePsi (fabiusLambertPhase x))) :=
      mapClusterPt_iff_of_tendsto_sub_zero
        (tendsto_fabiusWikipediaLambertRatio_sub_periodic F hF)
    _ ↔ z ∈ range (fun t : ℝ => Real.exp (negativeLaplacePsi t)) := by
      simpa only [Function.comp_def] using
        (mapClusterPt_periodic_comp_fabiusLambertPhase_iff
          hperiodic hcontinuous (z := z))
    _ ↔ z ∈ Icc (Real.exp negativeLaplacePsiPeriodMin)
          (Real.exp negativeLaplacePsiPeriodMax) := by
      rw [range_exp_negativeLaplacePsi_eq_Icc_periodExtrema]

private theorem fabiusWikipediaLambertRatio_isBoundedUnder_le
    (F : BoundedFabius) (hF : IsFabius F) :
    IsBoundedUnder (· ≤ ·) (nhdsWithin 0 (Ioi 0))
      (fabiusWikipediaLambertRatio F) := by
  have herror :=
    (tendsto_fabiusWikipediaLambertRatio_sub_periodic F hF).isBoundedUnder_le
  have hperiodic :
      IsBoundedUnder (· ≤ ·) (nhdsWithin 0 (Ioi 0))
        (fun x : ℝ =>
          Real.exp (negativeLaplacePsi (fabiusLambertPhase x))) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun x =>
      Real.exp_le_exp.mpr
        (negativeLaplacePsi_value_le_periodMax (fabiusLambertPhase x)))
  have hsum := isBoundedUnder_le_add herror hperiodic
  simpa only [Pi.add_def, sub_add_cancel] using hsum

private theorem fabiusWikipediaLambertRatio_isBoundedUnder_ge
    (F : BoundedFabius) (hF : IsFabius F) :
    IsBoundedUnder (· ≥ ·) (nhdsWithin 0 (Ioi 0))
      (fabiusWikipediaLambertRatio F) := by
  have herror :=
    (tendsto_fabiusWikipediaLambertRatio_sub_periodic F hF).isBoundedUnder_ge
  have hperiodic :
      IsBoundedUnder (· ≥ ·) (nhdsWithin 0 (Ioi 0))
        (fun x : ℝ =>
          Real.exp (negativeLaplacePsi (fabiusLambertPhase x))) :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun x =>
      Real.exp_le_exp.mpr
        (negativeLaplacePsiPeriodMin_le_value (fabiusLambertPhase x)))
  have hsum := isBoundedUnder_ge_add herror hperiodic
  simpa only [Pi.add_def, sub_add_cancel] using hsum

/-- The lower limit of the literal-factor quotient is the exponential of the
global minimum of the centered periodic correction. -/
theorem liminf_fabiusWikipediaLambertRatio_nhdsGT_zero_eq
    (F : BoundedFabius) (hF : IsFabius F) :
    liminf (fabiusWikipediaLambertRatio F)
        (nhdsWithin 0 (Ioi 0)) =
      Real.exp negativeLaplacePsiPeriodMin := by
  have hleExp : Real.exp negativeLaplacePsiPeriodMin ≤
      Real.exp negativeLaplacePsiPeriodMax :=
    Real.exp_le_exp.mpr negativeLaplacePsiPeriodMin_le_periodMax
  have hboundedAbove :=
    fabiusWikipediaLambertRatio_isBoundedUnder_le F hF
  have hboundedBelow :=
    fabiusWikipediaLambertRatio_isBoundedUnder_ge F hF
  have hleast := isLeast_mapClusterPt_liminf
    (u := fabiusWikipediaLambertRatio F)
    hboundedAbove.isCoboundedUnder_ge hboundedBelow
  apply le_antisymm
  · exact hleast.2
      ((mapClusterPt_fabiusWikipediaLambertRatio_nhdsGT_zero_iff F hF).mpr
        (left_mem_Icc.mpr hleExp))
  · exact
      ((mapClusterPt_fabiusWikipediaLambertRatio_nhdsGT_zero_iff F hF).mp
        hleast.1).1

/-- The upper limit of the literal-factor quotient is the exponential of the
global maximum of the centered periodic correction. -/
theorem limsup_fabiusWikipediaLambertRatio_nhdsGT_zero_eq
    (F : BoundedFabius) (hF : IsFabius F) :
    limsup (fabiusWikipediaLambertRatio F)
        (nhdsWithin 0 (Ioi 0)) =
      Real.exp negativeLaplacePsiPeriodMax := by
  have hleExp : Real.exp negativeLaplacePsiPeriodMin ≤
      Real.exp negativeLaplacePsiPeriodMax :=
    Real.exp_le_exp.mpr negativeLaplacePsiPeriodMin_le_periodMax
  have hboundedAbove :=
    fabiusWikipediaLambertRatio_isBoundedUnder_le F hF
  have hboundedBelow :=
    fabiusWikipediaLambertRatio_isBoundedUnder_ge F hF
  have hgreatest := isGreatest_mapClusterPt_limsup
    (u := fabiusWikipediaLambertRatio F)
    hboundedBelow.isCoboundedUnder_le hboundedAbove
  apply le_antisymm
  · exact
      ((mapClusterPt_fabiusWikipediaLambertRatio_nhdsGT_zero_iff F hF).mp
        hgreatest.1).2
  · exact hgreatest.2
      ((mapClusterPt_fabiusWikipediaLambertRatio_nhdsGT_zero_iff F hF).mpr
        (right_mem_Icc.mpr hleExp))

/-! ## Why no constant normalization can repair the online factor -/

/-- The literal multiplicative Lambert-W factor printed online is not an
asymptotic equivalent of a bounded Fabius solution. -/
theorem fabius_not_isEquivalent_WikipediaLambertFactor
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ ((fun x : ℝ => fabiusReal F x) ~[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => fabiusWikipediaLambertFactor x)) := by
  intro hequiv
  apply fabius_not_isEquivalent_exp_WikipediaLambertMain F hF
  refine hequiv.congr_right ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (exp_fabiusWikipediaLambertMain_eq_WikipediaLambertFactor hx).symm

/-- No constant multiplier repairs the literal online factor.  If such a
multiplier existed, the quotient would converge to that constant; its strict,
explicitly identified liminf/limsup gap rules this out, including for the zero
multiplier. -/
theorem fabius_not_isEquivalent_const_mul_WikipediaLambertFactor
    (F : BoundedFabius) (hF : IsFabius F) (c : ℝ) :
    ¬ ((fun x : ℝ => fabiusReal F x) ~[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => c * fabiusWikipediaLambertFactor x)) := by
  intro hequiv
  have hquotient :
      fabiusWikipediaLambertRatio F ~[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ =>
          (c * fabiusWikipediaLambertFactor x) /
            fabiusWikipediaLambertFactor x) :=
    hequiv.div
      (IsEquivalent.refl :
        (fun x : ℝ => fabiusWikipediaLambertFactor x)
          ~[nhdsWithin 0 (Ioi 0)]
            (fun x : ℝ => fabiusWikipediaLambertFactor x))
  have hratioConst :
      fabiusWikipediaLambertRatio F ~[nhdsWithin 0 (Ioi 0)]
        (fun _ : ℝ => c) := by
    refine hquotient.congr_right ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_div_cancel_right₀ c (fabiusWikipediaLambertFactor_pos hx).ne'
  have htendsto :
      Tendsto (fabiusWikipediaLambertRatio F)
        (nhdsWithin 0 (Ioi 0)) (nhds c) :=
    hratioConst.tendsto_const
  have hinf := htendsto.liminf_eq
  have hsup := htendsto.limsup_eq
  rw [liminf_fabiusWikipediaLambertRatio_nhdsGT_zero_eq F hF] at hinf
  rw [limsup_fabiusWikipediaLambertRatio_nhdsGT_zero_eq F hF] at hsup
  exact (ne_of_lt (Real.exp_lt_exp.mpr
    negativeLaplacePsiPeriodMin_lt_periodMax)) (hinf.trans hsup.symm)

end Fabius
