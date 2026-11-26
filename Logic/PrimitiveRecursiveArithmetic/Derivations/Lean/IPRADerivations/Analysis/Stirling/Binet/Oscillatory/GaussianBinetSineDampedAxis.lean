import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceDecay
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetExponentialIntegralGrid
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerPositiveAxis
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaTwoShiftSecants

/-!
# Real damping on the actual sine transform mesh

The real-axis original complex chart has exactly the real decay
exponent at the same rational product. The two actual exponential
names agree, retaining their original independently chosen radii
and observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineDampedAxis

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode)
open GaussianBinetExponentialIntegralGrid (row)
open GaussianCoefficientNameBounds (unit)
open GaussianEulerDecayMesh (observation)
open GaussianEulerDampedTimeRate (fraction_product)
open GaussianEulerIntegrandName (decayPoint decayF decayData)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianInverseBinomialRows (negative_congr)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianNameEquivalence (cross_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalSyntheticDivision (qmul_congr)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem real_argument (X D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    argument X zero D zero ≐ fraction X D :=
  GaussianGammaFiniteValueProperness.fraction_equal (native X zero zero) (scale X oneCode) D hD
    (GaussianLogGammaEulerPositiveAxis.native_axis_equal X zero (.orI₁ (.eqRefl _)))

theorem original_exponent (X D a b : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianBinetLaplaceExponential.exponent X zero D zero a b ≐ decayPoint (X*a) (D*b) :=
  (qmul_congr (negative_congr (real_argument X D hD)) (.eqRefl _)).eqTrans
    (((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      ((GaussianGammaDigammaTwoShiftSecants.negative_mul (fraction a b) (fraction X D)).eqSymm)).eqTrans
      (negative_congr ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (fraction_product X D a b hD hb))))

theorem same_observation (p q X D a b R T : PTm n) (hz : Γ ⊢[PRAAx] source X zero D zero R)
    (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (row p (qnegative (argument X zero D zero)) (R*T) a b)
      (observation (X*a) (D*b) q) (unit p+unit q) (unit p*unit q) := by
  let x := GaussianBinetLaplaceExponential.exponent X zero D zero a b
  let s := R*T
  let r := GaussianNameBounds.U constantF x
  have hu := GaussianSignedNameExponentialOrder.constant_input x s
    (GaussianBinetLaplaceExponential.exponent_bound X zero D zero R T a b hz hb ht)
  have hv := exponential_input (Γ := Γ) constantF x (constant_regular x)
  have eq := GaussianExponentialRadiusIndependence.same_input_cross constantF s r x hu hv
  have h := original_exponent X D a b hz.andE₁.andE₂ hb
  have hd : Γ ⊢[PRAAx] exponentialInputData constantF x ≐ decayData (X*a) (D*b) := by
    simpa only [exponentialInputData,decayData,GaussianRadiusExponentialName.subst_data,GaussianNameBounds.subst_U,
      Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (exponentialInputData constantF (var 0)) h
  exact distance_congr (.eqRefl _) (congrAp2 decayF (.eqRefl q) hd) (.eqRefl _) (.eqRefl _) (cross_at _ _ _ _ p q eq)

end LeanProofs.IPRA.Analysis.GaussianBinetSineDampedAxis
