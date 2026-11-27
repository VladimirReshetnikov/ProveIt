import IPRADerivations.Analysis.Trigonometry.MultipleAngles.GaussianNamedSineMultipleAngle
import IPRADerivations.Analysis.Trigonometry.SineProducts.SampleProducts.GaussianSineNormalizedSampleName
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff

/-!
# The normalized sine polynomial at the actual even recurrence

The reciprocal exponential pair gives a common finite evaluation
of the even trace recurrence and the polynomial in the original
sine. The factor 2J+1 clears the polynomial normalization.
-/

set_option autoImplicit false
set_option maxHeartbeats 280000

namespace LeanProofs.IPRA.Analysis.GaussianNamedEvenSinePolynomial

open_ipra
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianArctangentDivisionAngles (modulus)
open GaussianBoundedIntegerExponentialStages (scaledF stageData radius)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono_one)
open GaussianExponentialInverseSamples (positive negative exact_pair disk inverseDisk positive_bound negative_bound)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_refl)
open GaussianNamedSineFromExponential (sineF sineData sine_regular multiplier)
open GaussianNamedSineMultipleAngle (recurrenceF recurrenceData recurrenceRadius recurrence_regular recurrence_sample multipleF multipleData)
open GaussianNamedSineMultipleAngleSamples (baseRadius base_sample multiplier_unit_bound)
open GaussianRadiusExponentialName (input)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_symmetric)
open GaussianRationalHorner (qadd qmul evaluate canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone bound_congr bounded_difference bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianSineMultipleAngleRecurrence (evenValue)
open GaussianSineNormalizedSampleReconstruction (normalizedValue inverseOdd inverse_odd_unit)
open GaussianSinePolynomialVariation (variationBudget normalized_value_distance)
open GaussianSineSquaredTrace (fromSine sineValue evaluation_at_sine)
open GaussianSineSquaredPolynomial (coefficients)
open GaussianEuclideanDistanceName (pointCN)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sineDisk (f : PR 2) (R x : PTm n) : PTm n :=
  GaussianNameBounds.U (sineF f) (sineData f R x)+(disk R+inverseDisk f R x)

def polynomialF (f : PR 2) : PR 2 := GaussianSineNormalizedSampleName.polynomialF (sineF f)
def rootProductF (f : PR 2) : PR 2 := GaussianSineNormalizedSampleName.nameF (sineF f)
def polynomialData (f : PR 2) (J R x z : PTm n) : PTm n :=
  GaussianSineNormalizedSampleName.data J (sineDisk f R x) (sineData f R x) z

def scaledPolynomialF (f : PR 2) : PR 2 := multiplyF constantF (polynomialF f)
def scaledPolynomialData (f : PR 2) (J R x z : PTm n) : PTm n :=
  multiplyData constantF (polynomialF f) (naturalPoint (modulus J)) (polynomialData f J R x z)

ipra_subst sineDisk
ipra_subst polynomialData
ipra_subst scaledPolynomialData

theorem original_sine_bound (f : PR 2) (p R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (ap2 (sineF f) p (sineData f R x)) (sineDisk f R x) one :=
  bounded_radius_mono_one (le_add_right _ _) (GaussianNameBounds.sample_bound _ _ _ (sine_regular f R x hf))

theorem original_sine_bounds (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] GaussianSineNormalizedSampleName.bound (sineF f) (sineDisk f R x) (sineData f R x) := by
  refine .allI ?_
  have h : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using hf.shift
  simpa only [GaussianRootApproximationWitness.pointBounds,Syn.shift,GaussianNamedSineFromExponential.subst_sineData,subst_sineDisk] using
    original_sine_bound f (var 0) (Syn.shift R) (Syn.shift x) h

theorem reciprocal_pair_sine_bound (f : PR 2) (p R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (sineValue (positive f p R x) (negative f p R x)) (sineDisk f R x) one := by
  let C := disk R+inverseDisk f R x
  have hd : Γ ⊢[PRAAx] bounded (GaussianRationalMetric.qsub (positive f p R x) (negative f p R x)) C one :=
    bound_congr (.eqRefl _) (by dsimp only [C]; ipra_ring) (one_mul one)
      (bounded_difference _ _ _ _ _ _ (le_refl one) (le_refl one) (positive_bound f p R x hf) (negative_bound f p R x hf))
  have hs : Γ ⊢[PRAAx] bounded (sineValue (positive f p R x) (negative f p R x)) C one :=
    bound_congr (.eqRefl _) (one_mul C) (one_mul one)
      (bounded_product multiplier _ one one C one (le_refl one) (le_refl one) multiplier_unit_bound hd)
  exact bounded_radius_mono_one (le_add_left _ _) hs

theorem polynomial_regular (f : PR 2) (J R x z : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] pointCN (polynomialF f) (polynomialData f J R x z) :=
  GaussianSineNormalizedSampleName.polynomial_regular _ _ _ _ _ (sine_regular f R x hf) (original_sine_bounds f R x hf)

theorem root_product_cross (f : PR 2) (J R x z : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] crossEquivalent (rootProductF f) (polynomialF f) (polynomialData f J R x z) (polynomialData f J R x z) :=
  GaussianSineNormalizedSampleName.polynomial_cross _ _ _ _ _ (sine_regular f R x hf) (original_sine_bounds f R x hf)

theorem scaled_polynomial_regular (f : PR 2) (J R x z : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] pointCN (scaledPolynomialF f) (scaledPolynomialData f J R x z) :=
  multiply_fast _ _ _ _ (constant_regular _) (polynomial_regular f J R x z hf)

def polynomialRadius (f : PR 2) (J R x : PTm n) : PTm n :=
  (GaussianSineNormalizedSampleName.budget J (sineDisk f R x)+one)+variationBudget J (sineDisk f R x)*baseRadius f R x

ipra_subst polynomialRadius [one]

theorem polynomial_sample (f : PR 2) (p J R x z : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (polynomialF f) p (polynomialData f J R x z))
      (normalizedValue J (fromSine (sineValue (positive f p R x) (negative f p R x)))) (polynomialRadius f J R x) (unit p) := by
  let F := sineF f
  let X := sineData f R x
  let B := sineDisk f R x
  let L := GaussianSineNormalizedSampleName.budget J B
  have hp := unit_positive (Γ := Γ) p
  have reg := GaussianSineNormalizedSampleName.raw_polynomial_regular F J B X z (sine_regular f R x hf)
    (original_sine_bounds f R x hf)
  have first := GaussianNameRingLaws.normalized_to_sample (GaussianSineNormalizedSampleName.rawPolynomialF F) L
    (GaussianSineNormalizedSampleName.rawData J X z) p reg
  have normalized := distance_congr (.eqRefl _) (GaussianSineNormalizedSampleName.raw_polynomial_at F p J X z)
    (.eqRefl _) (.eqRefl _) first
  have last := normalized_value_distance J _ _ B _ _ hp (original_sine_bound f p R x hf)
    (reciprocal_pair_sine_bound f p R x hf) (base_sample f p R x hf)
  exact distance_triangle_same _ _ _ _ _ _ hp normalized last

theorem clear_normalization (A B J : PTm n) (hAB : Γ ⊢[PRAAx] qmul A B ≐ qone) :
    Γ ⊢[PRAAx] qmul (naturalPoint (modulus J)) (normalizedValue J (fromSine (sineValue A B))) ≐ evenValue (qadd A B) J := by
  let Q := evaluate (coefficients J) (fromSine (sineValue A B))
  have hQ : Γ ⊢[PRAAx] canonical Q := GaussianRationalHorner.horner_canonical _ _ _
  have h : Γ ⊢[PRAAx] qmul (naturalPoint (modulus J)) (inverseOdd J) ≐ qone :=
    (qmul_commutative (naturalPoint (modulus J)) (inverseOdd J)).eqTrans (inverse_odd_unit J)
  exact (qmul_associative (naturalPoint (modulus J)) (inverseOdd J) Q).eqSymm.eqTrans
    ((qmul_congr h (.eqRefl Q)).eqTrans ((qmul_commutative qone Q).eqTrans
      ((qmul_one_right Q hQ).eqTrans (evaluation_at_sine A B J hAB))))

def scaledPolynomialRadius (f : PR 2) (J R x z : PTm n) : PTm n :=
  (multiplyModulus constantF (polynomialF f) (naturalPoint (modulus J)) (polynomialData f J R x z)+one)+
    modulus J*polynomialRadius f J R x

ipra_subst scaledPolynomialRadius [one]

theorem scaled_polynomial_sample (f : PR 2) (p J R x z : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (scaledPolynomialF f) p (scaledPolynomialData f J R x z))
      (evenValue (qadd (positive f p R x) (negative f p R x)) J) (scaledPolynomialRadius f J R x z) (unit p) := by
  let m := modulus J
  let M := naturalPoint m
  let F := polynomialF f
  let X := polynomialData f J R x z
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have first := GaussianNameRingLaws.multiply_sample_error constantF F M X p (constant_regular M)
    (polynomial_regular f J R x z hf)
  have step := distance_congr (.eqRefl _) (qmul_congr (constant_at p M) (.eqRefl _)) (.eqRefl _) (.eqRefl _) first
  have second := multiply_distance M _ _ m _ U hp (GaussianNamedNaturalScale.natural_point_bound m)
    (polynomial_sample f p J R x z hf)
  exact distance_congr (.eqRefl _) (clear_normalization _ _ _ (exact_pair f p R x hf)) (.eqRefl _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp step second)

def bridgeRadius (f : PR 2) (J R x z : PTm n) : PTm n := recurrenceRadius f (two*J) R x+scaledPolynomialRadius f J R x z

ipra_subst bridgeRadius [two, one]

theorem even_recurrence_at (f : PR 2) (p J R x z : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (recurrenceF f) p (recurrenceData f (two*J) R x))
      (ap2 (scaledPolynomialF f) p (scaledPolynomialData f J R x z)) (bridgeRadius f J R x z) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p) (recurrence_sample f p (two*J) R x hf)
    (distance_symmetric _ _ _ _ (unit_positive p) (scaled_polynomial_sample f p J R x z hf))

theorem even_recurrence_cross (f : PR 2) (J R x z : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] crossEquivalent (recurrenceF f) (scaledPolynomialF f)
      (recurrenceData f (two*J) R x) (scaledPolynomialData f J R x z) := by
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (bridgeRadius f J R x z)
    (recurrence_regular f (two*J) R x hf) (scaled_polynomial_regular f J R x z hf)
  refine .allI ?_
  have h : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using hf.shift
  simpa only [GaussianNamedDiagonalRate.diagonalRate,Syn.shift,GaussianNamedSineMultipleAngle.subst_recurrenceData,
    subst_scaledPolynomialData,subst_bridgeRadius,PTm.subst_mul,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    even_recurrence_at f (var 0) (Syn.shift J) (Syn.shift R) (Syn.shift x) (Syn.shift z) h

def oddProductF (f : PR 2) : PR 2 := multiplyF (sineF f) (scaledPolynomialF f)
def oddProductData (f : PR 2) (J R x z : PTm n) : PTm n :=
  multiplyData (sineF f) (scaledPolynomialF f) (sineData f R x) (scaledPolynomialData f J R x z)

theorem odd_multiple_cross (f : PR 2) (E J R x z : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (hE : Γ ⊢[PRAAx] le (modulus J) E) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (scaledF f)) (oddProductF f)
      (sineData (scaledF f) (radius E R) (stageData E (modulus J) x)) (oddProductData f J R x z) := by
  have hs := sine_regular f R x hf
  have hrec := recurrence_regular f (two*J) R x hf
  have hp := scaled_polynomial_regular f J R x z hf
  have link : Γ ⊢[PRAAx] crossEquivalent (multipleF f) (oddProductF f) (multipleData f (two*J) R x)
      (oddProductData f J R x z) :=
    GaussianGammaAdjacentCutoff.multiply_cross _ _ _ _ _ _ _ _ hs hs hrec hp
      (cross_refl _ _ hs) (even_recurrence_cross f J R x z hf)
  exact cross_trans _ _ _ _ _ _ (GaussianNamedSineMultipleAngle.identity f E (two*J) R x hf hE) link

theorem actual_even_recurrence_normalized_sine_polynomial_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (input f (var 1) (var 2) ⟶ crossEquivalent (recurrenceF f) (scaledPolynomialF f)
        (recurrenceData f (two*var 0) (var 1) (var 2)) (scaledPolynomialData f (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (even_recurrence_cross f _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEvenSinePolynomial
