import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsParameterShift
import IPRADerivations.Analysis.Exponential.GaussianExponentialInverse
import IPRADerivations.Analysis.FiniteOperations.GaussianBoundedInverseApartness

/-!
# The actual scaling constant alpha^z and its original inverse

The constant alpha times the original Euler power alpha^(z/B-1) is the
original exponential with actual exponent (z/B)*log(alpha). The native
parameter-shift coefficient identity identifies its entire exponent
data, including the radius computed from its original zeroth sample.
The original exponential of the actual negative name is its inverse.
Its regularity supplies a finite reciprocal anchor; no nonzero or
inverse law is supplied as a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingConstant

open_ipra
open GaussianEulerIntegrandName (powerExponentF logarithmF coefficient powerExponentData powerData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (negativeF negativeData oneF)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianRationalHorner (ofGaussian qmul qadd)
open GaussianRationalMetric (qsub qnegative bounded)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (B c d : PTm n) : Fm PTm n := le one B ⋏ GaussianPositiveRationalLogarithm.source c d
abbrev exponentF : PR 2 := powerExponentF
def exponentData (z B c d : PTm n) : PTm n :=
  multiplyData constantF logarithmF (ofGaussian z B) (GaussianPositiveRationalLogarithm.data c d)
def radius (z B c d : PTm n) : PTm n := GaussianNameBounds.U exponentF (exponentData z B c d)
abbrev nameF : PR 2 := GaussianRadiusExponentialName.nameF exponentF
def data (z B c d : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius z B c d) (exponentData z B c d)
def exponentClock (p z B c d : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus constantF logarithmF (ofGaussian z B) (GaussianPositiveRationalLogarithm.data c d)) p
abbrev scaleF : PR 2 := GaussianEulerIntegrationByPartsParameterShift.powerProductF
def scaleData (z B c d : PTm n) : PTm n := GaussianEulerIntegrationByPartsParameterShift.powerProductData z B c d
abbrev inverseF : PR 2 := GaussianRadiusExponentialName.nameF (negativeF exponentF)
def inverseData (z B c d : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (radius z B c d) (negativeData (exponentData z B c d))
abbrev productF : PR 2 := multiplyF nameF inverseF
def productData (z B c d : PTm n) : PTm n := multiplyData nameF inverseF (data z B c d) (inverseData z B c d)
abbrev rightProductF : PR 2 := multiplyF inverseF nameF
def rightProductData (z B c d : PTm n) : PTm n := multiplyData inverseF nameF (inverseData z B c d) (data z B c d)
def inverseBound (z B c d : PTm n) : PTm n := GaussianNameBounds.U inverseF (inverseData z B c d)
def anchor (z B c d : PTm n) : PTm n :=
  GaussianBoundedInverseApartness.height nameF inverseF (data z B c d) (inverseData z B c d) (inverseBound z B c d)

ipra_subst source
ipra_subst exponentData
ipra_subst radius
ipra_subst data
ipra_subst inverseData
ipra_subst productData
ipra_subst rightProductData
ipra_subst inverseBound
ipra_subst anchor

theorem exponent_regular (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    pointCN exponentF (exponentData z B c d) :=
  multiply_fast constantF logarithmF _ _ (constant_regular _) (GaussianPositiveRationalLogarithm.name_regular c d h.andE₂)

theorem original_input (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input exponentF (radius z B c d) (exponentData z B c d) :=
  GaussianGammaFiniteApproximantName.exponential_input exponentF _ (exponent_regular z B c d h)

theorem name_regular (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    pointCN nameF (data z B c d) := GaussianRadiusExponentialName.name_regular _ _ _ (original_input z B c d h)

theorem exponent_at (p z B c d : PTm n) : Γ ⊢[PRAAx]
    ap2 exponentF p (exponentData z B c d) ≐ qmul (ofGaussian z B)
      (GaussianPositiveRationalLogarithm.sample (exponentClock p z B c d) c d) :=
  (GaussianNameArithmetic.multiply_at constantF logarithmF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem shifted_coefficient (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    coefficient (GaussianGammaEulerHeadShift.shifted z B) B ≐ ofGaussian z B :=
  (GaussianEulerIntegrationByPartsParameterShift.shifted_coefficient z B hB).eqTrans
    ((GaussianRationalLinearProduct.qadd_commutative _ _).eqTrans (GaussianEulerIntegrationByPartsLinear.coefficient_plus_one z B hB))

theorem shifted_exponent_data (z B c d : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    powerExponentData (GaussianGammaEulerHeadShift.shifted z B) B c d ≐ exponentData z B c d := by
  simpa only [powerExponentData,exponentData,GaussianNameArithmetic.subst_multiplyData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqCongr1 (multiplyData constantF logarithmF (var 0) (Syn.shift (GaussianPositiveRationalLogarithm.data c d)))
      (shifted_coefficient z B hB)

theorem shifted_power_data (z B c d : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    powerData (GaussianGammaEulerHeadShift.shifted z B) B c d ≐ data z B c d := by
  have e := shifted_exponent_data z B c d hB
  have r : Γ ⊢[PRAAx] GaussianNameBounds.U exponentF (powerExponentData (GaussianGammaEulerHeadShift.shifted z B) B c d) ≐ radius z B c d := by
    simpa only [radius,GaussianNameBounds.subst_U,Syn.subst_var,Syn.inst_zero] using
      Prf.eqCongr1 (GaussianNameBounds.U exponentF (var 0)) e
  exact congrPairT r e

theorem original_scaling_constant (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    crossEquivalent scaleF nameF (scaleData z B c d) (data z B c d) :=
  GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ (.eqRefl _) (shifted_power_data z B c d h.andE₁)
    (cross_symm _ _ _ _ (GaussianEulerIntegrationByPartsParameterShift.original_power_parameter_shift z B c d h))

theorem original_scaling_constant_right (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF GaussianEulerIntegrandName.powerF constantF) nameF
      (multiplyData GaussianEulerIntegrandName.powerF constantF (powerData z B c d) (GaussianPositiveRationalLogarithm.fraction c d))
      (data z B c d) :=
  cross_trans _ _ _ _ _ _ (GaussianNameRingLaws.multiply_commutative GaussianEulerIntegrandName.powerF constantF
    (powerData z B c d) (GaussianPositiveRationalLogarithm.fraction c d)
    (GaussianEulerIntegrandName.power_regular z B c d h) (constant_regular _)) (original_scaling_constant z B c d h)

theorem original_scaling_constant_symm (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    crossEquivalent nameF scaleF (data z B c d) (scaleData z B c d) :=
  cross_symm _ _ _ _ (original_scaling_constant z B c d h)

theorem inverse_input (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input (negativeF exponentF) (radius z B c d) (negativeData (exponentData z B c d)) :=
  GaussianExponentialInverse.negative_input exponentF _ _ (original_input z B c d h)

theorem inverse_regular (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    pointCN inverseF (inverseData z B c d) := GaussianRadiusExponentialName.name_regular _ _ _ (inverse_input z B c d h)

theorem inverse_exponent_at (p z B c d : PTm n) : Γ ⊢[PRAAx]
    ap2 (negativeF exponentF) p (negativeData (exponentData z B c d)) ≐ GaussianFastValueCut.recode
      (qsub GaussianRationalHorner.qzero
        (qmul (ofGaussian z B) (GaussianPositiveRationalLogarithm.sample
          (exponentClock (GaussianFastValueCut.exponent (one+one) p) z B c d) c d))) :=
  (GaussianNameRingLaws.negative_at exponentF _ p).eqTrans
    (GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) (exponent_at _ z B c d)))

theorem inverse_product (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    crossEquivalent productF oneF (productData z B c d) (exponentData z B c d) :=
  GaussianExponentialInverse.exponential_inverse exponentF _ _ (original_input z B c d h)

theorem right_inverse_product (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    crossEquivalent rightProductF oneF (rightProductData z B c d) (exponentData z B c d) :=
  cross_trans _ _ _ _ _ _ (GaussianNameRingLaws.multiply_commutative inverseF nameF
    (inverseData z B c d) (data z B c d) (inverse_regular z B c d h) (name_regular z B c d h)) (inverse_product z B c d h)

theorem inverse_sample_bound (p z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    bounded (ap2 inverseF p (inverseData z B c d)) (inverseBound z B c d) one :=
  GaussianNameBounds.sample_bound inverseF _ p (inverse_regular z B c d h)

theorem original_reciprocal_input (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    GaussianNameReciprocal.input nameF (anchor z B c d) (data z B c d) := by
  have bound : Γ ⊢[PRAAx] GaussianExponentialSmallPerturbation.smallSamples inverseF (inverseData z B c d) (inverseBound z B c d) one := by
    simpa only [GaussianExponentialSmallPerturbation.smallSamples,GaussianRootApproximationWitness.pointBounds,inverseBound,
      Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      GaussianNameBounds.all_samples_bounded inverseF _ (inverse_regular z B c d h)
  have product := cross_trans _ _ _ _ _ _ (inverse_product z B c d h)
    (GaussianBoundedInverseApartness.ones_equivalent (exponentData z B c d) (data z B c d))
  exact GaussianBoundedInverseApartness.bounded_inverse_input nameF inverseF _ _ _ one
    (GaussianNameBounds.U_positive inverseF _) (le_refl one) (name_regular z B c d h) (inverse_regular z B c d h) bound product

theorem original_reciprocal_is_inverse (z B c d : PTm n) (h : Γ ⊢[PRAAx] source B c d) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameReciprocal.nameF nameF) inverseF
      (GaussianNameReciprocal.nameData (anchor z B c d) (data z B c d)) (inverseData z B c d) := by
  have product := cross_trans _ _ _ _ _ _ (inverse_product z B c d h)
    (GaussianBoundedInverseApartness.ones_equivalent (exponentData z B c d) (data z B c d))
  exact GaussianBoundedInverseApartness.reciprocal_matches_inverse nameF inverseF _ _ _
    (name_regular z B c d h) (inverse_regular z B c d h) (original_reciprocal_input z B c d h).andE₂ product

theorem actual_original_positive_scaling_constant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ crossEquivalent scaleF nameF
      (scaleData (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_scaling_constant _ _ _ _ Prf.hyp0))

theorem actual_original_scaling_exponential_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶
      (crossEquivalent productF oneF (productData (var 0) (var 1) (var 2) (var 3)) (exponentData (var 0) (var 1) (var 2) (var 3)) ⋏
       GaussianNameReciprocal.input nameF (anchor (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.andI (inverse_product _ _ _ _ Prf.hyp0) (original_reciprocal_input _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingConstant
