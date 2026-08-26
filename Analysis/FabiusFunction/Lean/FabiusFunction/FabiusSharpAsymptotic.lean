import FabiusFunction.FabiusSaddleCentralLambert
import FabiusFunction.FabiusExplicitSharpTransfer
import FabiusFunction.FabiusWikipediaObstruction
import FabiusFunction.FabiusDyadicSharpAsymptotic
import FabiusFunction.PeriodicFourier
import FabiusFunction.FabiusQuotientExponentialMismatch

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

end Fabius
