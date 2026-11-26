import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaNative
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaLogShift
import IPRADerivations.Analysis.Stirling.GaussianStirlingRationalTelescopers

/-!
# Positive rational steps in the original Gamma derivative

The native shifted datum is transported to the positive rational
encoding (D*a+b)/(D*b). The coefficient of the Gamma recurrence
changes by exactly the native derivative step 1/D.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaDigammaNative (minimumDenominator step_source derivativeData derivative_regular original_derivative_rate)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qadd positive_product ofGaussian)
open GaussianRationalMetric (bounded qsub distanceBounded)
open GaussianStirlingGammaLogarithm (source arg gammaData gamma_source gamma_regular)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "qd" => GaussianNamedDifferenceQuotient.data gammaF gammaF
local notation "shifted" => GaussianEulerParameterExponentialIncrement.shifted

def neighborNumerator (a b D : PTm n) : PTm n := D*a+b
def neighborDenominator (b D : PTm n) : PTm n := b*D
def neighborData (a b D : PTm n) : PTm n := gammaData (neighborNumerator a b D) (neighborDenominator b D)
def stepQuotientData (a b D : PTm n) : PTm n := qd (neighborData a b D) (gammaData a b) oneCode D

theorem denominator_positive (p a b D : PTm n) (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) :
    Γ ⊢[PRAAx] le one D :=
  le_trans (unit_positive p) (le_trans (le_add_left _ _) hD)

theorem neighbor_source (a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] source (neighborNumerator a b D) (neighborDenominator b D) :=
  .andI (le_trans (positive_product _ _ hD hs.andE₁) (le_add_right _ _)) (positive_product _ _ hs.andE₂ hD)

private theorem shifted_value (a b D : PTm n) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal (shifted (arg a) b oneCode D) (arg (neighborNumerator a b D)) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianEulerParameterExponentialIncrement.shifted,arg,neighborNumerator,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring

set_option maxHeartbeats 800000 in
theorem neighbor_cross (p a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF
      (GaussianGammaReciprocalInverse.gammaData (shifted (arg a) b oneCode D) (a+one) (b*D) (two*b))
      (neighborData a b D) := by
  let z := shifted (arg a) b oneCode D
  let c := neighborNumerator a b D
  let d := neighborDenominator b D
  let w := arg c
  have hNative := GaussianGammaEulerFirstDerivative.shifted_source p (arg a) a b b oneCode D (step_source p a b D hs hD)
  have h1 := GaussianGammaHalfPlaneInputContinuity.reciprocal_source z (a+one) d (two*b) hNative
  have q := shifted_value (Γ := Γ) a b D
  have h2 := GaussianGammaInputProperness.gamma_source_equal z w (a+one) d one (two*b) h1 q
  have h3 := gamma_source c d (neighbor_source a b D hs (denominator_positive p a b D hD))
  exact cross_trans _ _ _ _ _ _ (GaussianGammaInputProperness.original_Gamma_proper z w (a+one) d one (two*b) h1 q)
    (GaussianGammaRadiusOverlap.original_Gamma_overlap w (a+one) c d one (two*b) one d h2 h3)

theorem quotient_cross (p a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) :
    Γ ⊢[PRAAx] crossEquivalent QF QF (GaussianGammaDigammaNative.quotientData a b D) (stepQuotientData a b D) := by
  let z := shifted (arg a) b oneCode D
  let y := GaussianGammaReciprocalInverse.gammaData z (a+one) (b*D) (two*b)
  have hNative := GaussianGammaEulerFirstDerivative.shifted_source p (arg a) a b b oneCode D (step_source p a b D hs hD)
  have regular := GaussianGammaReciprocalInverse.gamma_regular z (a+one) (b*D) one (two*b)
    (GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _ hNative)
  have hN := gamma_regular _ _ (neighbor_source a b D hs (denominator_positive p a b D hD))
  have h0 := gamma_regular a b hs
  exact GaussianNamedDifferenceQuotientProperness.proper gammaF gammaF gammaF gammaF y (neighborData a b D)
    (gammaData a b) (gammaData a b) oneCode D regular hN h0 h0
    (neighbor_cross p a b D hs hD) (cross_refl _ _ h0)

theorem step_rate (p a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) :
    Γ ⊢[PRAAx] independentRate QF IF (stepQuotientData a b D) (derivativeData a b) one (unit p) :=
  GaussianNamedRateTransport.transport QF IF QF IF _ _ _ _ one (unit p) (unit_positive p)
    (original_derivative_rate p a b D hs hD) (cross_symm _ _ _ _ (quotient_cross p a b D hs hD))
    (cross_refl _ _ (derivative_regular a b hs))

theorem unit_step_value (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] fraction one D ≐ ofGaussian oneCode D := by
  apply GaussianGammaFiniteValueProperness.fraction_equal _ _ _ hD
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring

theorem fraction_increment (a b D : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] fraction (neighborNumerator a b D) (neighborDenominator b D) ≐
      qadd (fraction a b) (fraction one D) :=
  (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by unfold neighborNumerator; ipra_ring) (.eqRefl _)).eqTrans
    (GaussianEulerPositivePowerChartCorrectedImage.fraction_sum a b one D hb hD).eqSymm

theorem coefficient_difference (a b D : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qsub (fraction (neighborNumerator a b D) (neighborDenominator b D)) (fraction a b) ≐ ofGaussian oneCode D := by
  have h := GaussianRationalHorner.ofGaussian_canonical (scale one oneCode) D hD
  exact (GaussianRationalSyntheticDivision.qsub_congr (fraction_increment a b D hb hD) (.eqRefl _)).eqTrans
    ((GaussianRationalSyntheticDivision.qadd_sub_cancel (fraction a b) (fraction one D) h).eqTrans (unit_step_value D hD))

theorem neighbor_coefficient_bound (a b D : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] bounded (fraction (neighborNumerator a b D) (neighborDenominator b D)) (a+one) one := by
  let m := neighborNumerator a b D
  let d := neighborDenominator b D
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ hb hD
  have e := GaussianEulerDecayFactorBounds.fraction_is_radius_point m d hd
  have h := GaussianRationalReciprocal.bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded m d hd)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hd (le_refl one) (by
    unfold m d neighborNumerator neighborDenominator
    ipra_le 𝔞 a*𝔞 D*sl hb+𝔞 b*sl hD) h

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaStep
