import IPRADerivations.Analysis.Gamma.NegativeAxis.Recurrence.GaussianGammaNegativeIntervalInverseRecurrence
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumSignedStep

/-!
# Literal signed steps to a thin chord center on a negative interval

The denominator and Gaussian increment are the same as on the positive
chord. The negative pole guards are preserved by the interpolation.
The rational step is exact for either endpoint order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalChordStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaMinimumSignedStep (centerNumerator centerDenominator increment increment_bounded separated_norm)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalNative (negative_regular data)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNamedDifferenceQuotient (input)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents positive_product represents_congr)
open GaussianRationalMetric (distanceBounded qsub qsub_canonical qsub_represents)
open GaussianRationalReciprocal (bound_congr)
open GaussianRootAlgebra (equal equal_of_values re_sub im_sub re_scale im_scale re_one im_one)
open GaussianStirlingGammaLogarithm (arg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem center_guard (a c b W : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hw : Γ ⊢[PRAAx] le one W) : Γ ⊢[PRAAx] guard (centerNumerator a c W) (centerDenominator b W) := by
  have e := natEq (LeanProofs.IPRA.AnalyticNumberTheory.BinomialThree.pos_of_one_le hw)
  have ha' := ha.andE₂
  have hc' := hc.andE₂
  unfold lt at ha' hc'
  refine .andI (le_trans hc.andE₁ (le_add_left _ _)) ?_
  unfold lt centerNumerator centerDenominator
  ipra_le 𝔞(pred W)*sl ha'+sl hc'+𝔞(pred W) with -𝔞(b)*e

private theorem increment_value (a c W : PTm n) (hw : Γ ⊢[PRAAx] le one W) :
    Γ ⊢[PRAAx] equal (GaussianRootAlgebra.sub (arg (centerNumerator a c W)) (arg (W*a))) (increment a c) := by
  have e := natEq (LeanProofs.IPRA.AnalyticNumberTheory.BinomialThree.pos_of_one_le hw)
  apply equal_of_values
  · simp only [arg,centerNumerator,increment,re_sub,re_scale,re_one,ComplexLogarithmRemainder.eval_re_code]
    simp only [ZT.toZ]
    ipra_simps
    linear_combination -𝔞(a)*e
  · simp only [arg,centerNumerator,increment,im_sub,im_scale,im_one,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring

theorem exact_increment (a c b W : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hw : Γ ⊢[PRAAx] le one W) :
    Γ ⊢[PRAAx] qsub (fraction (centerNumerator a c W) (centerDenominator b W))
      (fraction (W*a) (centerDenominator b W)) ≐ ofGaussian (increment a c) (centerDenominator b W) := by
  let D := centerDenominator b W
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hw hb
  have rep := qsub_represents (fraction (centerNumerator a c W) D) (fraction (W*a) D)
    (arg (centerNumerator a c W)) (arg (W*a)) D hD (ofGaussian_represents _ _ hD) (ofGaussian_represents _ _ hD)
  exact canonical_unique _ _ _ D (qsub_canonical _ _) (ofGaussian_canonical _ _ hD) hD
    (represents_congr (.eqRefl _) (increment_value a c W hw) (.eqRefl _) rep) (ofGaussian_represents _ _ hD)

theorem increment_distance (a c b W : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hw : Γ ⊢[PRAAx] le one W) : Γ ⊢[PRAAx]
    distanceBounded (fraction (centerNumerator a c W) (centerDenominator b W)) (fraction (W*a) (centerDenominator b W)) one W := by
  let D := centerDenominator b W
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hw hb
  have gap := LeanProofs.IPRA.Probability.MedianWeighted.ad_le_of
    (le_trans (le_of_lt hc.andE₂) (le_add_left b a)) (le_trans (le_of_lt ha.andE₂) (le_add_left b c))
  have cmp := le_congr (mul_comm _ _) ((mul_comm b W).eqTrans (one_mul D).eqSymm) (mul_le_mul_right W gap)
  exact bound_congr (exact_increment a c b W hb hw).eqSymm (.eqRefl _) (.eqRefl _)
    (increment_bounded a c D one W hD hw cmp)

def quotientData (a c b N W : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data gammaF gammaF (data (centerNumerator a c W) (centerDenominator b W) N)
    (data a b N) (increment a c) (centerDenominator b W)

theorem quotient_input (a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hw : Γ ⊢[PRAAx] le one W) (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a) : Γ ⊢[PRAAx]
    input gammaF gammaF (data (centerNumerator a c W) (centerDenominator b W) N)
      (data a b N) (increment a c) (centerDenominator b W) :=
  .andI (negative_regular _ _ _ (center_guard a c b W ha hc hw)) (.andI (negative_regular _ _ _ ha)
    (.andI (positive_product _ _ hw (le_trans ha.andE₁ (le_of_lt ha.andE₂))) (separated_norm a c apart)))

theorem actual_original_negative_Gamma_chord_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((guard (var 0) (var 2) ⋏ (guard (var 1) (var 2) ⋏ (le one (var 4) ⋏ (lt (var 0) (var 1) ⋎ lt (var 1) (var 0))))) ⟶
      (input gammaF gammaF (data (centerNumerator (var 0) (var 1) (var 4)) (centerDenominator (var 2) (var 4)) (var 3))
        (data (var 0) (var 2) (var 3)) (increment (var 0) (var 1)) (centerDenominator (var 2) (var 4)) ⋏
      distanceBounded (fraction (centerNumerator (var 0) (var 1) (var 4)) (centerDenominator (var 2) (var 4)))
        (fraction (var 4*var 0) (centerDenominator (var 2) (var 4))) one (var 4))) :=
  closeUniv 5 (.impI (.andI
    (quotient_input _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂)
    (increment_distance _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalChordStep
