import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.Chords.GaussianGammaNegativeIntervalChordStep
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.StepQuotients.GaussianGammaNegativeIntervalInverseStepCoefficient

/-!
# The original inverse shift coefficients on a signed thin chord

The base and chord center use a common denominator after exact
rescaling. Their inverse shift multipliers have a common bound on a
fixed pole-separated interval. The original product difference can
therefore be divided by the signed step with a uniform error.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalChordInverse

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaMinimumSignedStep (centerNumerator centerDenominator increment)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalChordStep (center_guard exact_increment increment_distance)
open GaussianGammaNegativeIntervalInverseBound (literal_inverse bound_from_margin)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse correctionFactor)
open GaussianGammaNegativeIntervalNative (product)
open GaussianGammaNegativeIntervalRescale (guard_rescale original_product_rescale)
open GaussianGammaNegativeProductDerivative (dividedDifference original_product_gap)
open GaussianGammaNegativeProductDerivativeInverse (inverseCoefficient inverse_coefficient_difference)
open GaussianGammaNegativeProductDerivativeInverseRate (inverseGapCost inverseRateCost original_inverse_gap_bound original_inverse_coefficient_rate)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (ofGaussian qmul canonical qmul_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qone)
open GaussianStirlingGammaLogarithm (arg)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def poleMargin (a b K : PTm n) : Fm PTm n := le b (K*a) ⋏ le b (K*monus b a)
def centerInverse (a c b N W : PTm n) : PTm n := inverse (centerNumerator a c W) (centerDenominator b W) N
def shiftCoefficient (a c b N W : PTm n) : PTm n :=
  dividedDifference (arg (W*a)) (arg (centerNumerator a c W)) (centerDenominator b W) (succ N)
def finiteInverseCoefficient (a c b N W : PTm n) : PTm n :=
  inverseCoefficient (centerInverse a c b N W) (inverse a b N) (shiftCoefficient a c b N W)

theorem center_margin (a c b K W : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hw : Γ ⊢[PRAAx] le one W) (hla : Γ ⊢[PRAAx] poleMargin a b K) (hlc : Γ ⊢[PRAAx] poleMargin c b K) :
    Γ ⊢[PRAAx] poleMargin (centerNumerator a c W) (centerDenominator b W) K := by
  let A := centerNumerator a c W
  let B := centerDenominator b W
  have hn := center_guard a c b W ha hc hw
  have ew := natEq (LeanProofs.IPRA.AnalyticNumberTheory.BinomialThree.pos_of_one_le hw)
  have ea := natEq (eq_add_of_le (le_of_lt ha.andE₂))
  have ec := natEq (eq_add_of_le (le_of_lt hc.andE₂))
  have em := natEq (eq_add_of_le (le_of_lt hn.andE₂))
  have eq : Γ ⊢[PRAAx] monus B A ≐ pred W*monus b a+monus b c := by
    apply deriveNat
    dsimp only [A,B,centerNumerator,centerDenominator] at em ⊢
    ipra_simps
    linear_combination -em+𝔞(pred W)*ea+ec+𝔞(b)*ew
  have first : Γ ⊢[PRAAx] le B (K*A) := by
    unfold A B centerNumerator centerDenominator
    ipra_le 𝔞(pred W)*sl hla.andE₁+sl hlc.andE₁ with -𝔞(b)*ew
  have rest : Γ ⊢[PRAAx] le B (K*(pred W*monus b a+monus b c)) := by
    unfold B centerDenominator
    ipra_le 𝔞(pred W)*sl hla.andE₂+sl hlc.andE₂ with -𝔞(b)*ew
  exact .andI first (le_congr (.eqRefl _) (congrMul (.eqRefl K) eq.eqSymm) rest)

theorem inverse_bound (a b K N : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hm : Γ ⊢[PRAAx] poleMargin a b K) :
    Γ ⊢[PRAAx] bounded (inverse a b N) (K*K) one :=
  bound_from_margin a b N (K*K) h (le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono hm.andE₁ hm.andE₂))

private theorem inverse_canonical (a b N : PTm n) : Γ ⊢[PRAAx] canonical (inverse a b N) :=
  qmul_canonical _ _

theorem exact_inverse_step (a c b N W : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hw : Γ ⊢[PRAAx] le one W) : Γ ⊢[PRAAx]
    qsub (centerInverse a c b N W) (inverse a b N) ≐
      qmul (ofGaussian (increment a c) (centerDenominator b W)) (finiteInverseCoefficient a c b N W) := by
  let a' := W*a
  let c' := centerNumerator a c W
  let b' := centerDenominator b W
  let P := product a b N
  let Q := product c' b' N
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have hb' := positive_product (Γ := Γ) _ _ hw hb
  have hn := center_guard a c b W ha hc hw
  have gap := (qsub_congr (.eqRefl Q) (original_product_rescale a b W N ha hw).eqSymm).eqTrans
    ((original_product_gap (arg a') (arg c') b' (succ N) hb').eqTrans
      (qmul_congr (exact_increment a c b W hb hw) (.eqRefl _)))
  exact inverse_coefficient_difference Q P _ _ _ _
    (inverse_canonical c' b' N) (inverse_canonical a b N)
    (literal_inverse c' b' N hn) (literal_inverse a b N ha) gap

theorem coefficient_rates (a c b N K W : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hw : Γ ⊢[PRAAx] le one W) (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c b K) :
    Γ ⊢[PRAAx] distanceBounded (centerInverse a c b N W) (inverse a b N) (inverseGapCost (succ N) (K*K)) W ⋏
      distanceBounded (finiteInverseCoefficient a c b N W) (correctionFactor a b N) (inverseRateCost (succ N) (K*K)) W := by
  let a' := W*a
  let b' := centerDenominator b W
  let c' := centerNumerator a c W
  let c₀ := inverse a b N
  let c₁ := centerInverse a c b N W
  let H := K*K
  have hBase := guard_rescale a b W ha hw
  have hCenter := center_guard a c b W ha hc hw
  have hc₀ : Γ ⊢[PRAAx] canonical c₀ := inverse_canonical a b N
  have hc₁ : Γ ⊢[PRAAx] canonical c₁ := inverse_canonical c' b' N
  have hi₀ : Γ ⊢[PRAAx] qmul (product a' b' N) c₀ ≐ qone :=
    (qmul_congr (original_product_rescale a b W N ha hw) (.eqRefl _)).eqTrans (literal_inverse a b N ha)
  have hi₁ := literal_inverse c' b' N hCenter
  have hb₀ := inverse_bound a b K N ha hma
  have hb₁ := inverse_bound c' b' K N hCenter (center_margin a c b K W ha hc hw hma hmc)
  have step := increment_distance a c b W ha hc hw
  have gap := original_inverse_gap_bound a' c' b' N c₁ c₀ H one W hBase hCenter hc₁ hc₀ hi₁ hi₀ hb₁ hb₀ hw step
  have rate := original_inverse_coefficient_rate a' c' b' N c₁ c₀ H one W hBase hCenter hc₁ hc₀ hi₁ hi₀ hb₁ hb₀ hw step
  have same := GaussianGammaNegativeCriticalRescale.correction_rescale a b N W ha hw
  exact .andI (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) gap)
    (distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) same) (by ipra_ring) (.eqRefl _) rate)

theorem actual_original_negative_Gamma_chord_inverse_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((guard (var 0) (var 2) ⋏ (guard (var 1) (var 2) ⋏ (le one (var 5) ⋏
       (poleMargin (var 0) (var 2) (var 4) ⋏ poleMargin (var 1) (var 2) (var 4))))) ⟶
      distanceBounded (centerInverse (var 0) (var 1) (var 2) (var 3) (var 5)) (inverse (var 0) (var 2) (var 3))
        (inverseGapCost (succ (var 3)) (var 4*var 4)) (var 5) ⋏
      distanceBounded (finiteInverseCoefficient (var 0) (var 1) (var 2) (var 3) (var 5)) (correctionFactor (var 0) (var 2) (var 3))
        (inverseRateCost (succ (var 3)) (var 4*var 4)) (var 5)) :=
  closeUniv 6 (.impI (coefficient_rates _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalChordInverse
