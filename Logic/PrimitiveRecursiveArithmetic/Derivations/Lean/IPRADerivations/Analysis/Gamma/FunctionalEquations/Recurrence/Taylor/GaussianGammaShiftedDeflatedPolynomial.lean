import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.Coefficients.GaussianGammaCanonicalPrefixTaylor
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaRepeatedShift
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.Continuity.GaussianGammaFiniteValueProperness
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalInverseQuadraticAlgebra

/-!
# Actual shifted P observations versus deflated original full polynomials

The zero constant coefficient factors the original full polynomial as
w times its actual Horner prefix. C20 and the original cofinal program
identify this prefix with P(w+1). The requested observations remain
independent; only the auxiliary recurrence observation is removed.
The numerical norm guard certifies the native increment is nonzero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaShiftedDeflatedPolynomial

open_ipra
open GaussianGammaOriginalC19Prefix (buffer totalDegree)
open GaussianGammaCanonicalExponent (source)
open GaussianRationalHorner (ofGaussian qmul horner hornerF positive_product)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (z R B : PTm n) : Fm PTm n := source z R B ⋏ le one (ComplexLogarithmRemainder.normSq z)
def rawValue (q z R B d : PTm n) : PTm n :=
  horner (buffer q R (succ d)) (ofGaussian z B) (totalDegree q R (succ d))
def shiftedSample (p z R B : PTm n) : PTm n := GaussianGammaRepeatedShift.stage p z R B one
def recurrenceCost (R : PTm n) : PTm n := GaussianGammaRepeatedShift.stepCost R one
def auxiliaryCost (R B : PTm n) : PTm n := one+B*(recurrenceCost R+one)
def numerator (p q B : PTm n) : PTm n := unit q+B*unit p
def denominator (p q : PTm n) : PTm n := unit p*unit q

ipra_subst input
ipra_subst rawValue
ipra_subst shiftedSample
ipra_subst recurrenceCost
ipra_subst auxiliaryCost
ipra_subst numerator
ipra_subst denominator

/-- This factorization is unconditional, even for a zero native input. -/
theorem original_buffer_factor (q z R B d : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (buffer q R (succ d)) (ofGaussian z B) ≐
      qmul (ofGaussian z B) (rawValue q z R B d) := by
  have shape := GaussianGammaFiniteCoefficientPolynomial.polynomial_length (Γ := Γ)
    (GaussianGammaCofinalCoefficientName.coefficientPrecision (GaussianGammaOriginalC19Prefix.stage q (succ d)) (two*R)) (two*R)
    (GaussianGammaCofinalCoefficientName.degreeCutoff (GaussianGammaOriginalC19Prefix.stage q (succ d)) (two*R))
    (GaussianGammaCofinalCoefficientName.exponentialCutoff (GaussianGammaOriginalC19Prefix.stage q (succ d)) (two*R))
  have constant := GaussianGammaPolynomialConstantLinear.whole_constant (Γ := Γ)
    (GaussianGammaCofinalCoefficientName.coefficientPrecision (GaussianGammaOriginalC19Prefix.stage q (succ d)) (two*R)) (two*R)
    (GaussianGammaCofinalCoefficientName.degreeCutoff (GaussianGammaOriginalC19Prefix.stage q (succ d)) (two*R))
    (GaussianGammaCofinalCoefficientName.exponentialCutoff (GaussianGammaOriginalC19Prefix.stage q (succ d)) (two*R))
  exact (congrAp3 hornerF shape (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalHorner.horner_succ _ _ _).eqTrans
      ((qadd_congr (.eqRefl _) constant).eqTrans
        ((GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
          (GaussianRationalPowerAlgebra.qmul_commutative _ _))))

theorem original_buffer_value (q z R B d : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianGammaCofinalCoefficientName.sample (GaussianGammaOriginalC19Prefix.stage q (succ d)) z (two*R) B ≐
      qmul (ofGaussian z B) (rawValue q z R B d) :=
  (GaussianGammaCofinalCoefficientName.actual_polynomial_observation _ _ _ _ hB).eqSymm.eqTrans
    (original_buffer_factor q z R B d)

theorem original_recurrence (s z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample s z R B) (qmul (ofGaussian z B) (shiftedSample s z R B))
      (recurrenceCost R) (unit s) := by
  have factor : Γ ⊢[PRAAx] GaussianGammaEulerHeadShift.linear z B zero ≐ ofGaussian z B :=
    (GaussianGammaShiftTrajectory.point_linear z B zero h.andE₂.andE₁).eqSymm.eqTrans
      (GaussianGammaFiniteValueProperness.fraction_equal _ _ B h.andE₂.andE₁
        (GaussianRootAlgebra.equal_of_code (GaussianGammaShiftTrajectory.point_zero z B)))
  exact distance_congr (GaussianGammaRepeatedShift.stage_zero s z R B) (qmul_congr factor (.eqRefl _))
    (.eqRefl _) (.eqRefl _) (GaussianGammaRepeatedShift.stage_step_error s z R B one zero h (zero_le one))

theorem raw_error (s q z R B d : PTm n) (h : Γ ⊢[PRAAx] input z R B) : Γ ⊢[PRAAx]
    distanceBounded (shiftedSample s z R B) (rawValue q z R B d)
      (B*(unit s+(recurrenceCost R+one)*unit q)) (unit s*unit q) := by
  have hs := unit_positive (Γ := Γ) s
  have hq := unit_positive (Γ := Γ) q
  have hd := positive_product _ _ hs hq
  have first := distance_radius_mono _ _ _ _ (recurrenceCost R*unit q) (unit s*unit q) hs hd
    (le_of_eq_add (d := zero) (by ipra_ring)) (distance_symmetric _ _ _ _ hs (original_recurrence s z R B h.andE₁))
  have last := distance_congr (.eqRefl _) (original_buffer_value q z R B d h.andE₁.andE₂.andE₁) (.eqRefl _) (.eqRefl _)
    (GaussianGammaOriginalC19Prefix.original_to_polynomial s q z R B (succ d) h.andE₁)
  have products := distance_triangle_same _ _ _ _ _ _ hd first last
  have sep : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated z B := .andI h.andE₁.andE₂.andE₁ h.andE₂
  have scaled := GaussianNamedDifferenceQuotient.scale_distance (GaussianNamedDifferenceQuotient.inverse z B) _ _ B
    (recurrenceCost R*unit q+(unit s+unit q)) (unit s*unit q) hd
    (GaussianNamedDifferenceQuotient.inverse_bound z B sep) products
  have law := GaussianNamedDifferenceQuotient.actual_inverse z B sep
  exact distance_congr
    (GaussianRationalInverseQuadraticAlgebra.cancel_nested_product _ _ _ (GaussianGammaC7Name.sample_canonical _ _ _ _) law)
    (GaussianRationalInverseQuadraticAlgebra.cancel_nested_product _ _ _ (GaussianRationalHorner.horner_canonical _ _ _) law)
    (by ipra_ring) (.eqRefl _) scaled

theorem original_auxiliary_error (p q s z R B d : PTm n) (h : Γ ⊢[PRAAx] input z R B) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (shiftedSample p z R B) (rawValue q z R B d))
      (numerator p q B) (denominator p q) (auxiliaryCost R B) s := by
  have near := GaussianNameEquivalence.point_at GaussianGammaC7Name.nameF (GaussianGammaRepeatedShift.stageData z R B one) p s
    (GaussianGammaRepeatedShift.stage_regular z R B one h.andE₁)
  have last := distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (mul_comm (unit s) (unit q))
    (raw_error s q z R B d h)
  have joined := GaussianRationalDistanceOrder.distance_triangle_common_factor _ _ _ _ (unit p) _ (unit q) (unit s)
    (unit_positive p) (unit_positive q) (unit_positive s) near last
  have arithmetic : Γ ⊢[PRAAx] (unit p+unit s)*unit q+B*(unit s+(recurrenceCost R+one)*unit q)*unit p ≐
      numerator p q B*unit s+auxiliaryCost R B*denominator p q := by unfold numerator auxiliaryCost denominator; ipra_ring
  have actual := distance_congr (.eqRefl _) (.eqRefl _) arithmetic (.eqRefl _) joined
  simpa only [GaussianRationalSlackRemoval.slack,GaussianRationalMetric.distanceBounded,unit,denominator,shiftedSample,
    GaussianGammaRepeatedShift.stage] using actual

def gapQuery (p q z R B d : PTm n) : PTm n := GaussianRationalSlackRemoval.precision
  (qsub (shiftedSample p z R B) (rawValue q z R B d)) (numerator p q B) (denominator p q) (auxiliaryCost R B)

/-- The exact independent radius is 2^(-p)+B*2^(-q). -/
theorem original_observations (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] input z R B) : Γ ⊢[PRAAx]
    distanceBounded (shiftedSample p z R B) (rawValue q z R B d) (numerator p q B) (denominator p q) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (auxiliaryCost R B)
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (original_auxiliary_error p q (gapQuery p q z R B d) z R B d h)

theorem actual_original_full_polynomial_deflation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalHorner.evaluate (buffer (var 0) (var 2) (succ (var 4))) (ofGaussian (var 1) (var 3)) ≐
      qmul (ofGaussian (var 1) (var 3)) (rawValue (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (original_buffer_factor _ _ _ _ _)
theorem actual_original_shifted_P_deflated_polynomial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 2) (var 3) (var 4) ⟶ distanceBounded (shiftedSample (var 0) (var 2) (var 3) (var 4))
      (rawValue (var 1) (var 2) (var 3) (var 4) (var 5)) (numerator (var 0) (var 1) (var 4)) (denominator (var 0) (var 1))) :=
  closeUniv 6 (.impI (original_observations _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaShiftedDeflatedPolynomial
