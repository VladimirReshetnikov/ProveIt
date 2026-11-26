import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.GaussianGammaNegativeIntervalInverseStepQuotient
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Original Gamma unit-step derivative on every negative interval

The differentiated inverse recurrence gives independent observation
rates for the two terms of the literal difference quotient. Uniform
coefficient bounds remove the step denominator from the error budget.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalDerivativeRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (shifted_source)
open GaussianGammaNegativeIntervalInverseRecurrence (inverse correctionFactor)
open GaussianGammaNegativeIntervalInverseStepCoefficient
  (neighborInverse finiteInverseCoefficient inverseCap coefficient_rates step_inside)
open GaussianGammaNegativeIntervalInverseStepQuotient (finiteF finiteData quotient_cross)
open GaussianGammaNegativeProductDerivativeInverseRate (inverseGapCost inverseRateCost)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNameEquivalence (cross_symm)
open GaussianNameRingLaws (three)
open GaussianRationalDistanceOrder (distance_radius_mono distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "g" => GaussianStirlingGammaLogarithm.gammaData
local notation "dg" => GaussianGammaDigammaNative.derivativeData
local notation "positiveQuotient" => GaussianGammaDigammaStep.stepQuotientData
local notation "minimumDenominator" => GaussianGammaDigammaNative.minimumDenominator
local notation "targetF" => GaussianGammaNegativeIntervalInverseRecurrence.targetF
local notation "targetData" => GaussianGammaNegativeIntervalInverseRecurrence.targetData
local notation "derivativeF" => GaussianGammaNegativeIntervalInverseRecurrence.derivativeF
local notation "derivativeData" => GaussianGammaNegativeIntervalInverseRecurrence.derivativeData
local notation "correctionData" => GaussianGammaNegativeIntervalInverseRecurrence.correctionData
local notation "targetQF" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "targetQD" => GaussianGammaNegativeIntervalDerivativeTarget.data

def eulerCap (a b : PTm n) : PTm n := U IF (dg (b+a) b)+three
def firstCost (a b N : PTm n) : PTm n := eulerCap a b*inverseGapCost (succ N) (inverseCap b)+b*b
def secondCost (a b N : PTm n) : PTm n := U gammaF (g (b+a) b)*inverseRateCost (succ N) (inverseCap b)
def cost (a b N : PTm n) : PTm n := firstCost a b N+secondCost a b N

private theorem uniform_bound_at (F G : PR 2) (x y A B t : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) (hy : Γ ⊢[PRAAx] pointCN G y)
    (hRate : Γ ⊢[PRAAx] independentRate F G x y A B) : Γ ⊢[PRAAx]
    bounded (ap2 F t x) (U G y+three) one := by
  have den := GaussianNamedInverseRate.denominator_positive B t zero hB
  have comparison : Γ ⊢[PRAAx] le (rateNumerator A B t zero*one) (three*rateDenominator B t zero) := by
    unfold rateNumerator rateDenominator three
    ipra_le 𝔞(unit t)*𝔞(unit zero)*sl hA+
      𝔞(B)*𝔞(unit zero)*sl (unit_positive t)+𝔞(B)*𝔞(unit t)*sl (unit_positive zero)
  have near := distance_radius_mono _ _ _ _ _ _ den (le_refl one) comparison (rate_at F G x y A B t zero hRate)
  have total := GaussianReconstructionRoots.norm_from_distance (ap2 F t x) (ap2 G zero y) three one (U G y) one
    (le_refl one) (le_refl one) near (GaussianNameBounds.sample_bound G y zero hy)
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) total

private theorem uniform_bound (F G : PR 2) (x y A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) (hy : Γ ⊢[PRAAx] pointCN G y)
    (hRate : Γ ⊢[PRAAx] independentRate F G x y A B) : Γ ⊢[PRAAx]
    sampleBound F x (U G y+three) := by
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have bs : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Syn.shift,Fm.shift,one] using hB.shift
  have aS : Δ ⊢[PRAAx] le (sh A) (sh B) := by simpa [Δ,sh,Syn.shift,Fm.shift] using hA.shift
  have ys : Δ ⊢[PRAAx] pointCN G (sh y) := by simpa [Δ,sh,Syn.shift,Fm.shift] using hy.shift
  have rs : Δ ⊢[PRAAx] independentRate F G (sh x) (sh y) (sh A) (sh B) :=
    by simpa [Δ,sh,Syn.shift,Fm.shift] using hRate.shift
  refine .allI ?_
  simpa only [sampleBound,sh,Syn.shift,PTm.subst_add,GaussianNameBounds.subst_U,three,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    uniform_bound_at F G (sh x) (sh y) (sh A) (sh B) (var 0) bs aS ys rs

private theorem constant_samples (x M : PTm n) (h : Γ ⊢[PRAAx] bounded x M one) :
    Γ ⊢[PRAAx] sampleBound constantF x M := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift x) (Syn.shift M) one :=
    by simpa [Fm.shift,Syn.shift,one] using h.shift
  refine .allI ?_
  exact bound_congr (constant_at (var 0) (Syn.shift x)).eqSymm (.eqRefl _) (.eqRefl _) hs

theorem derivative_part_rate (p a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (hE : Γ ⊢[PRAAx] le (minimumDenominator p (b+a) b) D)
    (delta : Γ ⊢[PRAAx] distanceBounded (neighborInverse a b N D) (inverse a b N) (inverseGapCost (succ N) (inverseCap b)) D) :
    Γ ⊢[PRAAx] independentRate (multiplyF constantF QF) derivativeF
      (multiplyData constantF QF (neighborInverse a b N D) (positiveQuotient (b+a) b D)) (derivativeData a b N)
      (firstCost a b N) (unit p) := by
  let x := neighborInverse a b N D
  let y := positiveQuotient (b+a) b D
  let u := inverse a b N
  let v := dg (b+a) b
  let A := inverseGapCost (succ N) (inverseCap b)
  let M := eulerCap a b
  let R := b*b
  have hp := unit_positive (Γ := Γ) p
  have hu : Γ ⊢[PRAAx] le (unit p) D := le_trans (le_add_left _ _) hE
  have hD := le_trans hp hu
  have hs := shifted_source a b h
  have hy := GaussianGammaDigammaDifferenceProduct.quotient_regular (b+a) b D hs hD
  have hv := GaussianGammaDigammaNative.derivative_regular (b+a) b hs
  have positiveRate := GaussianGammaDigammaStep.step_rate p (b+a) b D hs hE
  have hM := uniform_bound QF IF y v one (unit p) hp hp hv positiveRate
  have hR := constant_samples u R (GaussianGammaNegativeIntervalInverseBound.base_bound a b N h)
  have rate := GaussianNamedMultiplyRate.independent_rate constantF QF constantF IF x y u v A D one (unit p) M R
    hD hp (constant_regular x) hy (constant_regular u) hv hM hR
    (GaussianNamedAddRate.constant_rate x u A D hD delta) positiveRate
  exact GaussianNamedRateRadius.weaken (multiplyF constantF QF) derivativeF _ _ _ _ (firstCost a b N) (unit p)
    (positive_product _ _ hD hp) hp (by
      dsimp only [GaussianNamedMultiplyRate.leadingNumerator,GaussianNamedMultiplyRate.leadingDenominator,firstCost,M,R,A]
      ipra_le 𝔞(eulerCap a b)*𝔞(inverseGapCost (succ N) (inverseCap b))*𝔞(unit p)*sl hu) rate

theorem correction_part_rate (p a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hu : Γ ⊢[PRAAx] le (unit p) D)
    (delta : Γ ⊢[PRAAx] distanceBounded (finiteInverseCoefficient a b N D) (correctionFactor a b N)
      (inverseRateCost (succ N) (inverseCap b)) D) : Γ ⊢[PRAAx]
    independentRate (multiplyF constantF gammaF) (multiplyF constantF gammaF)
      (multiplyData constantF gammaF (finiteInverseCoefficient a b N D) (g (b+a) b)) (correctionData a b N)
      (secondCost a b N) (unit p) := by
  let x := finiteInverseCoefficient a b N D
  let y := g (b+a) b
  let u := correctionFactor a b N
  let A := inverseRateCost (succ N) (inverseCap b)
  let M := U gammaF y
  let R := U constantF u
  have hp := unit_positive (Γ := Γ) p
  have hD := le_trans hp hu
  have hy := GaussianStirlingGammaLogarithm.gamma_regular _ _ (shifted_source a b h)
  have rate := GaussianNamedMultiplyRate.independent_rate constantF gammaF constantF gammaF x y u y A D zero one M R
    hD (le_refl one) (constant_regular x) hy (constant_regular u) hy
    (all_samples_bounded gammaF y hy) (all_samples_bounded constantF u (constant_regular u))
    (GaussianNamedAddRate.constant_rate x u A D hD delta) (GaussianNamedAddRate.self_rate gammaF y hy)
  exact GaussianNamedRateRadius.weaken (multiplyF constantF gammaF) (multiplyF constantF gammaF) _ _ _ _
    (secondCost a b N) (unit p) (positive_product _ _ hD (le_refl one)) hp (by
      dsimp only [GaussianNamedMultiplyRate.leadingNumerator,GaussianNamedMultiplyRate.leadingDenominator,secondCost,M,R,A,y]
      ipra_le 𝔞(U gammaF (g (b+a) b))*𝔞(inverseRateCost (succ N) (inverseCap b))*sl hu) rate

theorem combined_rate (p a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (hr : Γ ⊢[PRAAx] le (two*b) D) (hE : Γ ⊢[PRAAx] le (minimumDenominator p (b+a) b) D) :
    Γ ⊢[PRAAx] independentRate finiteF targetF (finiteData a b N D) (targetData a b N) (cost a b N) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hu : Γ ⊢[PRAAx] le (unit p) D := le_trans (le_add_left _ _) hE
  have coeff := coefficient_rates a b N D h hr
  have first := derivative_part_rate p a b N D h hE coeff.andE₁
  have second := correction_part_rate p a b N D h hu coeff.andE₂
  have rate := GaussianNamedAddRate.independent_rate
    (multiplyF constantF QF) (multiplyF constantF gammaF) derivativeF (multiplyF constantF gammaF)
    _ _ _ _ (firstCost a b N) (unit p) (secondCost a b N) (unit p) hp hp first second
  exact GaussianNamedRateRadius.weaken finiteF targetF _ _ _ _ (cost a b N) (unit p)
    (positive_product _ _ hp hp) hp (by
      dsimp only [GaussianNamedAddRate.leadingNumerator,GaussianNamedAddRate.leadingDenominator,cost]
      ipra_le 0) rate

theorem original_derivative_rate (p a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (hr : Γ ⊢[PRAAx] le (two*b) D) (hE : Γ ⊢[PRAAx] le (minimumDenominator p (b+a) b) D) :
    Γ ⊢[PRAAx] independentRate QF targetQF (GaussianGammaNegativeIntervalStep.data a b N D) (targetQD a b N)
      (cost a b N) (unit p) :=
  GaussianNamedRateTransport.transport finiteF targetF QF targetQF
    (finiteData a b N D) (targetData a b N) (GaussianGammaNegativeIntervalStep.data a b N D) (targetQD a b N)
    (cost a b N) (unit p) (unit_positive p) (combined_rate p a b N D h hr hE) (quotient_cross a b N D h hr)
    (cross_symm _ _ _ _ (GaussianGammaNegativeIntervalInverseRecurrence.target_cross a b N h))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalDerivativeRate
