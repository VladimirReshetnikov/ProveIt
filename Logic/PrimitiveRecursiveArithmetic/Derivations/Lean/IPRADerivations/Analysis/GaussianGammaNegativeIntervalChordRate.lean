import IPRADerivations.Analysis.GaussianGammaNegativeIntervalChordQuotient
import IPRADerivations.Analysis.GaussianNamedAddRate
import IPRADerivations.Analysis.GaussianNamedRateRadius

/-!
# Signed thin-chord derivative rate on a negative Gamma interval

The exact quotient product rule separates the positive Euler derivative
and the finite inverse shift coefficients. The pole margins bound the
inverse at both input points, and the chord denominator accommodates the
dyadic accuracy required by the positive quotient and the coefficients.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalChordRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFactorBudget (power_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaMinimumSignedStep (centerNumerator centerDenominator increment separated_norm weight)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (shifted_source)
open GaussianGammaNegativeIntervalChordInverse (poleMargin centerInverse finiteInverseCoefficient
  coefficient_rates center_margin inverse_bound)
open GaussianGammaNegativeIntervalChordQuotient (finiteF finiteData positive_center_regular translated_apart quotient_cross)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse derivativeF derivativeData correctionFactor correctionData targetF targetData)
open GaussianGammaNegativeProductDerivativeInverseRate (inverseGapCost inverseRateCost)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNamedRateComposition (symmetric)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianStirlingGammaLogarithm (gammaData gamma_regular)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "DG" => GaussianGammaDigammaNative.derivativeData
local notation "PQ" => GaussianGammaMinimumSignedStep.quotientData
local notation "NQ" => GaussianGammaNegativeIntervalChordStep.quotientData
local notation "TF" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "TD" => GaussianGammaNegativeIntervalDerivativeTarget.data

def chordWeight (p a b : PTm n) : PTm n := weight p (b+a) b two
def firstCost (a b N K : PTm n) : PTm n := U IF (DG (b+a) b)*inverseGapCost (succ N) (K*K)+K*K
def secondCost (a b N K : PTm n) : PTm n := U gammaF (gammaData (b+a) b)*inverseRateCost (succ N) (K*K)
def cost (a b N K : PTm n) : PTm n := firstCost a b N K+secondCost a b N K

theorem unit_le_chord_weight (p a b : PTm n) : Γ ⊢[PRAAx] le (unit p) (chordWeight p a b) := by
  let r := p+num 6
  let R := b+a
  let E := GaussianEulerLogarithmicContinuity.intervalDen r one R b
  let T := GaussianEulerLogarithmicContinuity.intervalTop r one R b
  let G := GaussianEulerLogarithmicContinuity.compactGain one R E T
  have hT : Γ ⊢[PRAAx] le one T := GaussianGammaIntegralCutoffs.top_positive _ _ _
  have hlog : Γ ⊢[PRAAx] le one (GaussianEulerLogarithmicMultiplier.logRadius E T) := by
    unfold GaussianEulerLogarithmicMultiplier.logRadius GaussianCompactLogarithmBounds.radius
    ipra_le 𝔞(E)*(𝔞(T)+1)+24
  have hthree : Γ ⊢[PRAAx] le one (num 3) := by ipra_le 2
  have hmajor : Γ ⊢[PRAAx] le one (GaussianEulerLogarithmicMultiplier.majorant (succ one) R E T) :=
    positive_product _ _ (power_positive _ _ hthree) (power_positive _ _ hlog)
  have gain : Γ ⊢[PRAAx] le one G := positive_product _ _ hT (le_trans hmajor (le_add_left _ _))
  have mod : Γ ⊢[PRAAx] le (unit r) (GaussianEulerLogarithmicContinuity.modulus r one R b) :=
    le_trans (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (unit r) gain)) (le_add_left _ _)
  have rise : Γ ⊢[PRAAx] le (unit p) (unit r) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  change Γ ⊢[PRAAx] le (unit p) (two+two*GaussianEulerLogarithmicContinuity.modulus r one R b)
  ipra_le 2*sl mod+sl rise+𝔞(unit r)+2

private theorem positive_domain (a c b : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b) :
    Γ ⊢[PRAAx] GaussianGammaMinimumSignedStep.domain (b+a) (b+c) b two :=
  .andI (shifted_source a b ha) (.andI (shifted_source c b hc).andE₁
    (.andI (by ipra_le sl (le_of_lt ha.andE₂)) (by ipra_le sl (le_of_lt hc.andE₂))))

private theorem constant_samples (x M : PTm n) (h : Γ ⊢[PRAAx] bounded x M one) :
    Γ ⊢[PRAAx] sampleBound constantF x M := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift x) (Syn.shift M) one :=
    by simpa [Fm.shift, Syn.shift, one] using h.shift
  refine .allI ?_
  exact bound_congr (constant_at (var 0) (Syn.shift x)).eqSymm (.eqRefl _) (.eqRefl _) hs

private theorem derivative_part_rate (p a c b N K : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a)
    (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c b K)
    (delta : Γ ⊢[PRAAx] distanceBounded (centerInverse a c b N (chordWeight p a b)) (inverse a b N)
      (inverseGapCost (succ N) (K*K)) (chordWeight p a b)) :
    Γ ⊢[PRAAx] independentRate derivativeF (multiplyF constantF QF) (derivativeData a b N)
      (multiplyData constantF QF (centerInverse a c b N (chordWeight p a b)) (PQ (b+a) (b+c) b (chordWeight p a b)))
      (firstCost a b N K) (unit p) := by
  let W := chordWeight p a b
  let A := inverseGapCost (succ N) (K*K)
  let R := K*K
  let u := inverse a b N
  let z := centerInverse a c b N W
  let v := DG (b+a) b
  let x := PQ (b+a) (b+c) b W
  let M := U IF v
  have hp := unit_positive (Γ := Γ) p
  have hu := unit_le_chord_weight (Γ := Γ) p a b
  have hw := le_trans hp hu
  have hs := shifted_source a b ha
  have hav := translated_apart a c b apart
  have hy := gamma_regular _ _ hs
  have hz := positive_center_regular a c b W hc hw
  have sep : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated (increment (b+a) (b+c)) (centerDenominator b W) :=
    .andI (GaussianGammaMinimumSignedStep.denominator_positive b W hs.andE₂ hw) (separated_norm _ _ hav)
  have hx : Γ ⊢[PRAAx] pointCN QF x := GaussianNamedDifferenceQuotient.name_regular _ _ _ _ _ _ (.andI hz (.andI hy sep))
  have hv := GaussianGammaDigammaNative.derivative_regular (b+a) b hs
  have positiveRate := GaussianGammaMinimumSignedStep.original_chord_quotient_rate p (b+a) (b+c) b two
    (positive_domain a c b ha hc) hav
  have hR := constant_samples z R (inverse_bound (centerNumerator a c W) (centerDenominator b W) K N
    (GaussianGammaNegativeIntervalChordStep.center_guard a c b W ha hc hw) (center_margin a c b K W ha hc hw hma hmc))
  have coefficient := GaussianNamedAddRate.constant_rate u z A W hw (distance_symmetric _ _ _ _ hw delta)
  have rate := GaussianNamedMultiplyRate.independent_rate constantF IF constantF QF u v z x A W one (unit p) M R
    hw hp (constant_regular u) hv (constant_regular z) hx (all_samples_bounded IF v hv) hR
    coefficient (symmetric QF IF x v one (unit p) hp positiveRate)
  exact GaussianNamedRateRadius.weaken derivativeF (multiplyF constantF QF) _ _ _ _ (firstCost a b N K) (unit p)
    (positive_product _ _ hw hp) hp (by
      dsimp only [GaussianNamedMultiplyRate.leadingNumerator, GaussianNamedMultiplyRate.leadingDenominator, firstCost, M, R, A, v]
      ipra_le 𝔞(U IF (DG (b+a) b))*𝔞(inverseGapCost (succ N) (K*K))*𝔞(unit p)*sl hu) rate

private theorem correction_part_rate (p a c b N K : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (delta : Γ ⊢[PRAAx] distanceBounded (finiteInverseCoefficient a c b N (chordWeight p a b)) (correctionFactor a b N)
      (inverseRateCost (succ N) (K*K)) (chordWeight p a b)) :
    Γ ⊢[PRAAx] independentRate (multiplyF constantF gammaF) (multiplyF constantF gammaF) (correctionData a b N)
      (multiplyData constantF gammaF (finiteInverseCoefficient a c b N (chordWeight p a b)) (gammaData (b+a) b))
      (secondCost a b N K) (unit p) := by
  let W := chordWeight p a b
  let u := correctionFactor a b N
  let z := finiteInverseCoefficient a c b N W
  let y := gammaData (b+a) b
  let A := inverseRateCost (succ N) (K*K)
  let M := U gammaF y
  let R := U constantF z
  have hp := unit_positive (Γ := Γ) p
  have hu := unit_le_chord_weight (Γ := Γ) p a b
  have hw := le_trans hp hu
  have hy := gamma_regular _ _ (shifted_source a b ha)
  have coefficient := GaussianNamedAddRate.constant_rate u z A W hw (distance_symmetric _ _ _ _ hw delta)
  have rate := GaussianNamedMultiplyRate.independent_rate constantF gammaF constantF gammaF u y z y A W zero one M R
    hw (le_refl one) (constant_regular u) hy (constant_regular z) hy
    (all_samples_bounded gammaF y hy) (all_samples_bounded constantF z (constant_regular z))
    coefficient (GaussianNamedAddRate.self_rate gammaF y hy)
  exact GaussianNamedRateRadius.weaken (multiplyF constantF gammaF) (multiplyF constantF gammaF) _ _ _ _
    (secondCost a b N K) (unit p) (positive_product _ _ hw (le_refl one)) hp (by
      dsimp only [GaussianNamedMultiplyRate.leadingNumerator, GaussianNamedMultiplyRate.leadingDenominator, secondCost, M, R, A, y]
      ipra_le 𝔞(U gammaF (gammaData (b+a) b))*𝔞(inverseRateCost (succ N) (K*K))*sl hu) rate

theorem finite_rate (p a c b N K : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a) (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c b K) :
    Γ ⊢[PRAAx] independentRate finiteF targetF (finiteData a c b N (chordWeight p a b))
      (targetData a b N) (cost a b N K) (unit p) := by
  let W := chordWeight p a b
  have hp := unit_positive (Γ := Γ) p
  have hw := le_trans hp (unit_le_chord_weight p a b)
  have coeff := coefficient_rates a c b N K W ha hc hw hma hmc
  have first := derivative_part_rate p a c b N K ha hc apart hma hmc coeff.andE₁
  have second := correction_part_rate p a c b N K ha coeff.andE₂
  have rate := GaussianNamedAddRate.independent_rate derivativeF (multiplyF constantF gammaF)
    (multiplyF constantF QF) (multiplyF constantF gammaF)
    _ _ _ _ (firstCost a b N K) (unit p) (secondCost a b N K) (unit p) hp hp first second
  have shrunk := GaussianNamedRateRadius.weaken targetF finiteF (targetData a b N) (finiteData a c b N W) _ _
    (cost a b N K) (unit p) (positive_product _ _ hp hp) hp (by
      dsimp only [GaussianNamedAddRate.leadingNumerator, GaussianNamedAddRate.leadingDenominator, cost]
      ipra_le 0) rate
  exact symmetric targetF finiteF _ _ (cost a b N K) (unit p) hp shrunk

theorem original_derivative_rate (p a c b N K : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a) (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c b K) :
    Γ ⊢[PRAAx] independentRate QF TF (NQ a c b N (chordWeight p a b)) (TD a b N) (cost a b N K) (unit p) := by
  let W := chordWeight p a b
  have hp := unit_positive (Γ := Γ) p
  have hw := le_trans hp (unit_le_chord_weight p a b)
  exact GaussianNamedRateTransport.transport finiteF targetF QF TF (finiteData a c b N W) (targetData a b N)
    (NQ a c b N W) (TD a b N) (cost a b N K) (unit p) hp
    (finite_rate p a c b N K ha hc apart hma hmc) (quotient_cross a c b N W ha hc hw apart)
    (cross_symm _ _ _ _ (GaussianGammaNegativeIntervalInverseRecurrence.target_cross a b N ha))

theorem actual_original_negative_Gamma_thin_chord_derivative_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((guard (var 1) (var 3) ⋏ (guard (var 2) (var 3) ⋏ ((lt (var 1) (var 2) ⋎ lt (var 2) (var 1)) ⋏
      (poleMargin (var 1) (var 3) (var 5) ⋏ poleMargin (var 2) (var 3) (var 5))))) ⟶
      independentRate QF TF (NQ (var 1) (var 2) (var 3) (var 4) (chordWeight (var 0) (var 1) (var 3)))
        (TD (var 1) (var 3) (var 4)) (cost (var 1) (var 3) (var 4) (var 5)) (unit (var 0))) :=
  closeUniv 6 (.impI (original_derivative_rate _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalChordRate
