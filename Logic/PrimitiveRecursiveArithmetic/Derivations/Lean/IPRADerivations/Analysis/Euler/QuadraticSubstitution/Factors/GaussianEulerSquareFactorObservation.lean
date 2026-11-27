import IPRADerivations.Analysis.Euler.QuadraticSubstitution.Kernels.GaussianEulerSquareIntegrand
import IPRADerivations.Analysis.Euler.QuadraticSubstitution.Kernels.GaussianEulerQuadraticKernelCompactName
import IPRADerivations.Analysis.Euler.QuadraticSubstitution.Jacobian.GaussianEulerSquareJacobianCompactName
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalSlackRemoval

/-!
# Independent original observations in quadratic Euler factorization

The raw Jacobian observation has its genuine amplification 2*c*T.
The actual retiming pays its requested observation error. At any later
auxiliary precision the original normalized quadratic identity and real
product error compare it to one fixed factor and kernel observation.
One explicit finite integer gap removes only the auxiliary error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquareFactorObservation

open_ipra
open GaussianEulerSquareIntegrand (factorF factorData jacobianF jacobianData factoredKernelF factoredKernelData)
open GaussianEulerSquareKernel (doubled kernelF kernelData)
open GaussianEulerSquareTimeGeometry (source)
open GaussianCompactLogarithmBounds (domain)
open GaussianEulerSquareJacobianRate (rawSample amplification)
open GaussianNameArithmetic (multiplyModulus)
open GaussianNameEquivalence (point_at cross_at)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def factorBound (z B c d : PTm n) : PTm n := GaussianNameBounds.U factorF (factorData z B c d)
def kernelBound (R E T c : PTm n) : PTm n := GaussianEulerQuadraticKernelTimeRate.majorant (two*R) E T c
def leadingNumerator (p q r K F : PTm n) : PTm n := unit q*unit r+K*unit p*unit r+F*unit p*unit q
def leadingDenominator (p q r : PTm n) : PTm n := unit p*unit q*unit r
def auxiliaryCost (z R B E T c d a b : PTm n) : PTm n := amplification T c+two+
  (multiplyModulus factorF kernelF (factorData z B c d) (kernelData (doubled z B) B a b c d)+one)+
    kernelBound R E T c+factorBound z B c d

ipra_subst factorBound [GaussianEulerSquareIntegrand.factorData, GaussianEulerPositiveScalingConstant.scaleData]
ipra_subst kernelBound
ipra_subst leadingNumerator
ipra_subst leadingDenominator

theorem denominator_positive (p q r : PTm n) : Γ ⊢[PRAAx] le one (leadingDenominator p q r) :=
  positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive r)

theorem positive_source (z R B E c d a b T : PTm n) (hs : Γ ⊢[PRAAx] source z R B E c d)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx] GaussianEulerPositiveScalingIntegrand.source B a b c d :=
  .andI hs.andE₁.andE₁ (.andI hs.andE₂ ht.andE₁)

theorem factor_regular (z R B E c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B E c d) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN factorF (factorData z B c d) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (GaussianGammaCanonicalExponent.constant_regular _)
    (GaussianEulerPositiveScalingCancellation.scale_regular z B c d (.andI hs.andE₁.andE₁ hs.andE₂))

theorem kernel_regular (z R B E T c d a b : PTm n) (hs : Γ ⊢[PRAAx] source z R B E c d)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN kernelF (kernelData (doubled z B) B a b c d) :=
  GaussianEulerSquareKernel.kernel_regular (doubled z B) B a b c d (positive_source z R B E c d a b T hs ht)

theorem kernel_observation_bound (s z R B E T c d a b : PTm n) (hs : Γ ⊢[PRAAx] source z R B E c d)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (ap2 kernelF s (kernelData (doubled z B) B a b c d)) (kernelBound R E T c) one :=
  GaussianEulerQuadraticKernelTimeRate.original_observation_bound s (doubled z B) (two*R) B E T c d a b
    (GaussianEulerQuadraticKernelTimeRate.doubled_source z R B E c d hs) ht

/-- Original raw drift at two actual clocks, with the requested retimed
Jacobian allowance paid by Fast(2*c*T,p). -/
theorem retimed_to_named (p s z R B E T c d a b : PTm n) (hs : Γ ⊢[PRAAx] source z R B E c d)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    distanceBounded
      (ap3 GaussianEulerSquareJacobianCompactName.evaluatorF p (pairT a b) (GaussianEulerSquareJacobianCompactName.fixedData z B c d T))
      (ap2 jacobianF s (jacobianData z B a b c d)) (unit s+amplification T c*unit p) (unit p*unit s) := by
  let X := GaussianEulerSquareJacobianRate.query p T c
  let Y := GaussianEulerSquareIntegrand.query s z B a b c d
  let J := amplification T c
  have xp : Γ ⊢[PRAAx] le (J*unit p) (unit X) := GaussianFastValueCut.query_budget J p
  have ys : Γ ⊢[PRAAx] le (unit s) (unit Y) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have raw := GaussianEulerSquareJacobianRate.raw_observations X Y z R B E T c d a b a b zero one hs ht ht (le_refl one)
    (GaussianRationalPowerDifference.distance_refl_zero _ one (le_refl one))
  have near := distance_radius_mono _ _ _ _ (unit s+J*unit p) (unit p*unit s)
    (GaussianNamedInverseRate.denominator_positive one X Y (le_refl one)) (positive_product _ _ (unit_positive p) (unit_positive s))
    (by dsimp only [GaussianEulerSquareJacobianRate.rawNumerator,GaussianNamedInverseRate.rateDenominator]
        ipra_le (𝔞(unit s)*𝔞(unit Y))*sl xp+(𝔞(J)*𝔞(unit p)*𝔞(unit X))*sl ys) raw
  exact distance_congr (GaussianEulerSquareJacobianCompactName.evaluator_at p (pairT a b) z B c d T).eqSymm
    (GaussianEulerSquareIntegrand.jacobian_sample s z B a b c d).eqSymm (.eqRefl _) (.eqRefl _) near

theorem observation_slack (p q r s z R B E T c d a b : PTm n) (hs : Γ ⊢[PRAAx] source z R B E c d)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    distanceBounded
      (ap3 GaussianEulerSquareJacobianCompactName.evaluatorF p (pairT a b) (GaussianEulerSquareJacobianCompactName.fixedData z B c d T))
      (qmul (ap2 factorF q (factorData z B c d)) (ap2 kernelF r (kernelData (doubled z B) B a b c d)))
      (leadingNumerator p q r (kernelBound R E T c) (factorBound z B c d)*unit s+
        auxiliaryCost z R B E T c d a b*leadingDenominator p q r) (leadingDenominator p q r*unit s) := by
  let V := leadingDenominator p q r
  let D := V*unit s
  let K := kernelBound R E T c
  let F := factorBound z B c d
  let x := factorData z B c d
  let y := kernelData (doubled z B) B a b c d
  have hD := positive_product _ _ (denominator_positive (Γ := Γ) p q r) (unit_positive s)
  have hp := factor_regular z R B E c d hs
  have hk := kernel_regular z R B E T c d a b hs ht
  have first := distance_radius_mono _ _ _ _ ((unit s+amplification T c*unit p)*(unit q*unit r)) D
    (positive_product _ _ (unit_positive p) (unit_positive s)) hD
    (le_of_eq_add (d := zero) (by dsimp only [D,V,leadingDenominator]; ipra_ring)) (retimed_to_named p s z R B E T c d a b hs ht)
  have equivalent := cross_at _ _ _ _ s s (GaussianEulerSquareIntegrand.original_quadratic_integrand z B a b c d (positive_source z R B E c d a b T hs ht))
  have second := distance_radius_mono _ _ _ _ (two*V) D
    (positive_product _ _ (unit_positive s) (unit_positive s)) hD
    (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)) equivalent
  have third := distance_radius_mono _ _ _ _ ((multiplyModulus factorF kernelF x y+one)*V) D (unit_positive s) hD
    (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)) (GaussianNameRingLaws.multiply_sample_error factorF kernelF x y s hp hk)
  have leftRate := distance_radius_mono _ _ _ _ ((unit s+unit q)*(unit p*unit r)) D
    (positive_product _ _ (unit_positive s) (unit_positive q)) hD
    (le_of_eq_add (d := zero) (by dsimp only [D,V,leadingDenominator]; ipra_ring)) (point_at factorF x s q hp)
  have rightRate := distance_radius_mono _ _ _ _ ((unit s+unit r)*(unit p*unit q)) D
    (positive_product _ _ (unit_positive s) (unit_positive r)) hD
    (le_of_eq_add (d := zero) (by dsimp only [D,V,leadingDenominator]; ipra_ring)) (point_at kernelF y s r hk)
  have fourth := GaussianNameArithmetic.product_distance _ _ _ _ _ _ D K F hD leftRate rightRate
    (kernel_observation_bound s z R B E T c d a b hs ht) (GaussianNameBounds.sample_bound factorF x q hp)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [leadingNumerator,auxiliaryCost,D,V,K,F,x,y,leadingDenominator]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first (distance_triangle_same _ _ _ _ _ _ hD second
      (distance_triangle_same _ _ _ _ _ _ hD third fourth)))

/-- Three independent original observations; only the auxiliary
precision is removed, using one explicitly computed finite query. -/
theorem original_point_bound (p q r z R B E T c d a b : PTm n) (hs : Γ ⊢[PRAAx] source z R B E c d)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    distanceBounded
      (ap3 GaussianEulerSquareJacobianCompactName.evaluatorF p (pairT a b) (GaussianEulerSquareJacobianCompactName.fixedData z B c d T))
      (qmul (ap2 factorF q (factorData z B c d)) (ap2 kernelF r (kernelData (doubled z B) B a b c d)))
      (leadingNumerator p q r (kernelBound R E T c) (factorBound z B c d)) (leadingDenominator p q r) := by
  apply GaussianRationalSlackRemoval.slack_removal_at _ _ _ (auxiliaryCost z R B E T c d a b) (denominator_positive p q r)
  exact observation_slack p q r _ z R B E T c d a b hs ht

theorem actual_original_quadratic_factor_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    ((source (var 3) (var 4) (var 5) (var 6) (var 8) (var 9) ⋏ domain (var 10) (var 11) (var 6) (var 7)) ⟶
      distanceBounded
        (ap3 GaussianEulerSquareJacobianCompactName.evaluatorF (var 0) (pairT (var 10) (var 11))
          (GaussianEulerSquareJacobianCompactName.fixedData (var 3) (var 5) (var 8) (var 9) (var 7)))
        (qmul (ap2 factorF (var 1) (factorData (var 3) (var 5) (var 8) (var 9)))
          (ap2 kernelF (var 2) (kernelData (doubled (var 3) (var 5)) (var 5) (var 10) (var 11) (var 8) (var 9))))
        (leadingNumerator (var 0) (var 1) (var 2) (kernelBound (var 4) (var 6) (var 7) (var 8)) (factorBound (var 3) (var 5) (var 8) (var 9)))
        (leadingDenominator (var 0) (var 1) (var 2))) :=
  closeUniv 12 (.impI (original_point_bound _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerSquareFactorObservation
