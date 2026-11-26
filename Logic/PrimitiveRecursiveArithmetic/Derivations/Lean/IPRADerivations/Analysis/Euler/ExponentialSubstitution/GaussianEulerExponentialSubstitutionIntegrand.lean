import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingConstant
import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsParameterShiftObservation

/-!
# Actual original Euler pullback under the exponential substitution

At positive rational t, the original named product t*Euler(z,t) is
cross-equivalent to the original exponential of (z/B)*log(t)-t.
The logarithm and exponential programs are unchanged. The shifted
Euler exponent, radius and full data are identified exactly before
using the checked parameter-shift identity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialSubstitutionIntegrand

open_ipra
open GaussianGammaEulerHeadShift (shifted)
open GaussianEulerIntegrandName (source logarithmF powerExponentF decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_at)
open GaussianRationalHorner (qmul qadd ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev exponentF : PR 2 := GaussianEulerIntegrandName.exponentF
def exponentData (z B a b : PTm n) : PTm n :=
  addData (GaussianEulerPositiveScalingConstant.exponentData z B a b) (decayPoint a b)
def radius (z B a b : PTm n) : PTm n := GaussianNameBounds.U exponentF (exponentData z B a b)
abbrev exponentialF : PR 2 := GaussianRadiusExponentialName.nameF exponentF
def data (z B a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius z B a b) (exponentData z B a b)
abbrev productF : PR 2 := GaussianEulerIntegrationByPartsParameterShift.productF
abbrev productData := @GaussianEulerIntegrationByPartsParameterShift.productData
abbrev evaluatorF : PR 3 := GaussianEulerIntegrandName.evaluatorF
def fixedData (z B : PTm n) : PTm n := GaussianEulerIntegrandName.fixedData (shifted z B) B
def sample (p z B a b : PTm n) : PTm n :=
  ap3 evaluatorF p (GaussianEulerIntegrandName.timeData a b) (fixedData z B)
def logarithmClock (p z B a b : PTm n) : PTm n := GaussianEulerPositiveScalingConstant.exponentClock
  (GaussianFastValueCut.exponent two p) z B a b

ipra_subst exponentData
ipra_subst radius
ipra_subst data
ipra_subst fixedData [shifted]
ipra_subst sample
ipra_subst logarithmClock [GaussianEulerPositiveScalingConstant.exponentClock]

theorem exponent_at (p z B a b : PTm n) : Γ ⊢[PRAAx]
    ap2 exponentF p (exponentData z B a b) ≐ qadd
      (qmul (ofGaussian z B) (GaussianPositiveRationalLogarithm.sample (logarithmClock p z B a b) a b)) (decayPoint a b) :=
  (GaussianNameArithmetic.add_at powerExponentF constantF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qadd_congr
      (GaussianEulerPositiveScalingConstant.exponent_at _ z B a b) (GaussianGammaCanonicalExponent.constant_at _ _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _)))

theorem exponent_regular (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx] pointCN exponentF (exponentData z B a b) :=
  add_fast powerExponentF constantF _ _ (GaussianEulerPositiveScalingConstant.exponent_regular z B a b h) (constant_regular _)

theorem exponential_input (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input exponentF (radius z B a b) (exponentData z B a b) :=
  GaussianGammaFiniteApproximantName.exponential_input exponentF _ (exponent_regular z B a b h)

theorem name_regular (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx] pointCN exponentialF (data z B a b) :=
  GaussianRadiusExponentialName.name_regular exponentF _ _ (exponential_input z B a b h)

theorem shifted_exponent_data (z B a b : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.exponentData (shifted z B) B a b ≐ exponentData z B a b :=
  GaussianGammaCompactCutoffSplit.add_data_congr _ _ _ _
    (GaussianEulerPositiveScalingConstant.shifted_exponent_data z B a b hB) (.eqRefl _)

theorem shifted_data (z B a b : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.data (shifted z B) B a b ≐ data z B a b := by
  have e := shifted_exponent_data z B a b hB
  have r : Γ ⊢[PRAAx] GaussianEulerIntegrandName.radius (shifted z B) B a b ≐ radius z B a b := by
    simpa only [GaussianEulerIntegrandName.radius,radius,GaussianNameBounds.subst_U,Syn.subst_var,Syn.inst_zero] using
      Prf.eqCongr1 (GaussianNameBounds.U exponentF (var 0)) e
  exact congrPairT r e

theorem sample_at (p z B a b : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    sample p z B a b ≐ ap2 exponentialF p (data z B a b) :=
  (GaussianEulerIntegrandName.sample_at p (shifted z B) B a b).eqTrans (congrAp2 exponentialF (.eqRefl p) (shifted_data z B a b hB))

theorem original_pullback (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    crossEquivalent productF exponentialF (productData z B a b) (data z B a b) :=
  GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ (.eqRefl _) (shifted_data z B a b h.andE₁)
    (cross_symm _ _ _ _ (GaussianEulerIntegrationByPartsParameterShift.original_integrand_parameter_shift z B a b h))

theorem original_observations (p q z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 productF p (productData z B a b)) (ap2 exponentialF q (data z B a b))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_pullback z B a b h)

theorem original_raw_observations (p q z B a b T : PTm n) (h : Γ ⊢[PRAAx] source z B a b)
    (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 exponentialF p (data z B a b))
      (qmul (GaussianPositiveRationalLogarithm.fraction a b) (GaussianEulerIntegrandName.sample q z B a b))
      (unit q+T*unit p) (unit p*unit q) :=
  GaussianRationalDistanceOrder.distance_congr (sample_at p z B a b h.andE₁) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianEulerIntegrationByPartsParameterShiftObservation.original_observations p q z B a b T h ht)

theorem actual_original_exponential_substitution_integrand_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent productF exponentialF
      (productData (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_pullback _ _ _ _ Prf.hyp0))

theorem actual_exponential_substitution_independent_raw_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 2) (var 3) (var 4) (var 5) ⋏ le (var 4) (var 6*var 5)) ⟶
      distanceBounded (ap2 exponentialF (var 0) (data (var 2) (var 3) (var 4) (var 5)))
        (qmul (GaussianPositiveRationalLogarithm.fraction (var 4) (var 5)) (GaussianEulerIntegrandName.sample (var 1) (var 2) (var 3) (var 4) (var 5)))
        (unit (var 1)+var 6*unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 7 (.impI (original_raw_observations _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialSubstitutionIntegrand
