import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaDerivativeAtOne
import IPRADerivations.Analysis.Stirling.Wallis.GaussianStirlingWallisGammaRatio
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicImproperInputProperness
import IPRADerivations.Analysis.Stirling.GammaLogarithm.GaussianStirlingGammaLogarithm
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaEncodingRescaling

/-!
# The original digamma name on positive rational inputs

The original first logarithmic Euler integral is the numerator, and
the original entire reciprocal Gamma program supplies the inverse.
Actual positive rational steps of the original Gamma name converge
to the numerator with the existing derivative rate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaNative

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative multiply_one_left oneF one_fast)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalSyntheticDivision (qone)
open GaussianStirlingGammaLogarithm (source arg gammaData gamma_source gamma_regular euler_real_source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "PF" => GaussianGammaC7Name.nameF
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF

def derivativeData (a b : PTm n) : PTm n := GaussianEulerLogarithmicImproperName.data one (arg a) a b b
def reciprocalData (a b : PTm n) : PTm n := GaussianGammaC7Name.data (arg a) a b
abbrev nameF : PR 2 := multiplyF PF IF
def data (a b : PTm n) : PTm n := multiplyData PF IF (reciprocalData a b) (derivativeData a b)
def modulus (p a b : PTm n) : PTm n := GaussianEulerLogarithmicContinuity.modulus (p+num 6) one a b
def minimumDenominator (p a b : PTm n) : PTm n := modulus p a b+unit p
def quotientData (a b D : PTm n) : PTm n :=
  GaussianGammaEulerFirstDerivative.quotientData (arg a) a b b oneCode D

ipra_subst derivativeData [one]

ipra_subst reciprocalData

ipra_subst data

ipra_subst modulus [one]

ipra_subst minimumDenominator

theorem derivative_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN IF (derivativeData a b) :=
  GaussianEulerLogarithmicImproperName.name_regular _ _ _ _ _ (euler_real_source a b hs).andE₁

theorem reciprocal_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN PF (reciprocalData a b) :=
  GaussianGammaC7Name.name_regular _ _ _ (gamma_source a b hs).andE₁

theorem name_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN nameF (data a b) :=
  multiply_fast _ _ _ _ (reciprocal_regular a b hs) (derivative_regular a b hs)

theorem step_source (p a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) :
    Γ ⊢[PRAAx] GaussianGammaEulerFirstDerivative.source p (arg a) a b b oneCode D := by
  have hd := le_trans (unit_positive p) (le_trans (le_add_left _ _) hD)
  have hm := GaussianEulerLogarithmicContinuity.modulus_positive (Γ := Γ) (p+num 6) one a b
  have sm := GaussianGammaUnitEulerDifference.increment_bound (modulus p a b) D hm (le_trans (le_add_right _ _) hD)
  exact .andI (.andI (.andI (euler_real_source a b hs).andE₁ (.andI hd sm))
    (le_congr (.eqRefl _) ComplexLogarithmRemainder.normSq_one.eqSymm (le_refl one))) hs.andE₁

theorem original_derivative_rate (p a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) :
    Γ ⊢[PRAAx] independentRate QF IF (quotientData a b D) (derivativeData a b) one (unit p) :=
  GaussianGammaEulerFirstDerivative.original_first_derivative_rate p (arg a) a b b oneCode D (step_source p a b D hs hD)

theorem derivative_quotient_regular (p a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hD : Γ ⊢[PRAAx] le (minimumDenominator p a b) D) :
    Γ ⊢[PRAAx] pointCN QF (quotientData a b D) :=
  GaussianGammaEulerFirstDerivative.quotient_regular p (arg a) a b b oneCode D (step_source p a b D hs hD)

theorem gamma_times_digamma (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF gammaF nameF) IF (multiplyData gammaF nameF (gammaData a b) (data a b))
      (derivativeData a b) := by
  let x := gammaData a b
  let y := reciprocalData a b
  let z := derivativeData a b
  let F := multiplyF gammaF PF
  let v := multiplyData gammaF PF x y
  have hx := gamma_regular a b hs
  have hy := reciprocal_regular a b hs
  have hz := derivative_regular a b hs
  have e := cross_trans _ _ _ _ _ _ (multiply_commutative gammaF PF x y hx hy)
    (cross_trans _ _ _ _ _ _ (GaussianGammaReciprocalInverse.gamma_product (arg a) a b one b (gamma_source a b hs))
      (GaussianBoundedInverseApartness.ones_equivalent y z))
  have last := multiply_cross F oneF IF IF v z z z (multiply_fast _ _ _ _ hx hy) (one_fast z)
    hz hz e (cross_refl _ _ hz)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative gammaF PF IF x y z hx hy hz))
    (cross_trans _ _ _ _ _ _ last (multiply_one_left _ _ hz))

theorem one_integral (hs : Γ ⊢[PRAAx] source one one) :
    Γ ⊢[PRAAx] crossEquivalent IF IF (derivativeData one one) (GaussianGammaUnitEulerDifference.integralData : PTm n) := by
  have ez : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (arg one) oneCode := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [arg,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring
  have eq := GaussianGammaFiniteValueProperness.fraction_equal _ _ one (le_refl one) ez
  apply GaussianEulerLogarithmicImproperInputProperness.original_improper_proper one (arg one) oneCode one one one one one one
  exact .andI (euler_real_source one one hs).andE₁ (.andI GaussianEulerUnitNormalization.unit_lower_source eq)

theorem digamma_one :
    Γ ⊢[PRAAx] crossEquivalent nameF GaussianGammaDerivativeAtOne.negativeGammaF (data one one)
      GaussianGammaDerivativeAtOne.negativeGammaData := by
  let y : PTm n := data one one
  let w : PTm n := gammaData one one
  have hs : Γ ⊢[PRAAx] source one one := .andI (le_refl one) (le_refl one)
  have hy := name_regular _ _ hs
  have hw := gamma_regular _ _ hs
  have eg := cross_trans _ _ _ _ _ _ (GaussianStirlingWallisGammaRatio.integer_factorial_cross (Γ := Γ) zero)
    (GaussianSignedNameExponentialOrder.constant_equal_cross _ _ GaussianGammaFactorialValues.factorial_zero)
  have g1 := cross_trans _ _ _ _ _ _ eg
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ GaussianGammaEncodingRescaling.one_constant_cross)
      (GaussianBoundedInverseApartness.ones_equivalent zero y))
  have trim := multiply_cross gammaF oneF nameF nameF w y y y hw (one_fast y) hy hy
    g1 (cross_refl _ _ hy)
  exact cross_trans _ _ _ _ _ _
    (cross_symm _ _ _ _ (multiply_one_left _ _ hy))
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ trim)
      (cross_trans _ _ _ _ _ _ (gamma_times_digamma one one hs)
        (cross_trans _ _ _ _ _ _ (one_integral hs)
          GaussianGammaDerivativeAtOne.original_logarithmic_integral_one_is_negative_gamma)))

theorem actual_positive_rational_digamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶
      crossEquivalent (multiplyF gammaF nameF) IF
        (multiplyData gammaF nameF (gammaData (var 0) (var 1)) (data (var 0) (var 1)))
        (derivativeData (var 0) (var 1))) :=
  closeUniv 2 (.impI (gamma_times_digamma _ _ Prf.hyp0))

theorem actual_digamma_at_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    crossEquivalent nameF GaussianGammaDerivativeAtOne.negativeGammaF (data one one)
      GaussianGammaDerivativeAtOne.negativeGammaData :=
  digamma_one

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaNative
