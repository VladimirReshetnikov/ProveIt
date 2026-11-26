import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerCompatibility
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerRationalPowerReference
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayRealSamples

/-!
# Real Euler powers above time one are at least the reciprocal time

The native real nonnegative parameter gives z/B-1>=-1. The same actual
ordered harmonic-log observation is multiplied by these two real
coefficients at one common clock. This derives signed exponential order
from the input alone and retains the original Euler power operation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerRealPowerLowerOrder

open_ipra
open GaussianEulerIntegrandName (coefficient powerExponentF powerExponentData powerRadius powerF powerData)
open GaussianEulerUpperPowerOrder (inputF expF product_input product_real_samples)
open GaussianRationalHorner (qmul represents canonical_unique represents_congr)
open GaussianRationalMetric (bounded qnegative qnegative_represents)
open GaussianRationalConjugation (point point_represents)
open GaussianRationalSyntheticDivision (qone)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianNamedPositiveExponentialOrder (sampleOrder realOrder)
open ComplexLogarithmRemainder (re im oneCode scale)
open RationalGaussianEmbedding (axis)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def realNonnegative (z : PTm n) : Fm PTm n := zle (ZT.ofNat zero) (re z) ⋏ ZT.eq (im z) (ZT.ofNat zero)
def source (z R B a b : PTm n) : Fm PTm n := GaussianEulerUpperPowerCoefficients.source z R B ⋏
  (realNonnegative z ⋏ (GaussianPositiveRationalLogarithm.source a b ⋏ le b a))
def reference : PTm n := qnegative qone
def amplification (R : PTm n) : PTm n := R+one
def referenceData (R a b : PTm n) : PTm n := GaussianBoundedConstantProductName.data
  (amplification R) reference (GaussianHarmonicLogarithmName.data a b)
def coefficientData (z R B a b : PTm n) : PTm n := GaussianBoundedConstantProductName.data
  (amplification R) (coefficient z B) (GaussianHarmonicLogarithmName.data a b)
def radius (R a : PTm n) : PTm n := amplification R*GaussianHarmonicLogarithmName.radius one a
def referenceExpData (R a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius R a) (referenceData R a b)
def coefficientExpData (z R B a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius R a) (coefficientData z R B a b)
ipra_subst realNonnegative
ipra_subst source
ipra_subst reference [qone]
ipra_subst amplification
ipra_subst referenceData
ipra_subst coefficientData

theorem coefficient_axis (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) : Γ ⊢[PRAAx] axis (coefficient z B) := by
  let g := GaussianRootAlgebra.sub z (scale B oneCode)
  have rep := GaussianEulerIntegrandName.coefficient_represents (Γ := Γ) z B hB
  have fixed : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (GaussianRationalReciprocal.conjugate g) g := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [GaussianRationalReciprocal.re_conjugate]
    · simp only [GaussianRationalReciprocal.im_conjugate,g,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one]
      rw [ZT.toZ_eq hi]
      ipra_simps
      ring
  have eq : Γ ⊢[PRAAx] point (coefficient z B) ≐ coefficient z B :=
    canonical_unique _ _ g B (GaussianRationalConjugation.point_canonical _)
      (GaussianRationalMetric.qsub_canonical _ _) hB
      (represents_congr (.eqRefl _) fixed (.eqRefl _) (point_represents _ _ _ hB rep)) rep
  exact RationalGaussianEmbedding.axis_congr (GaussianEulerDecayRealSamples.fixed_axis_embedding _ eq)
    (RationalGaussianEmbedding.embed_axis _)

theorem coefficient_lower (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] zle (ZT.ofNat zero) (re z)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (reference : PTm n)) (fstT (coefficient z B)) := by
  let g := GaussianRootAlgebra.sub z (scale B oneCode)
  let negOne : PTm n := ComplexLogarithmRemainder.neg oneCode
  have lr := qnegative_represents (Γ := Γ) qone oneCode one (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one))
  have rr := GaussianEulerIntegrandName.coefficient_represents (Γ := Γ) z B hB
  apply RationalArithmetic.order_of_representations _ _ (re negOne) (re g) one B
    lr.andE₁ rr.andE₁ (le_refl one) hB
  apply zle_of_toZ (LeanProofs.IPRA.PTm.monus ((re z).pos+(ZT.ofNat zero).neg) ((ZT.ofNat zero).pos+(re z).neg))
  have e := zle_toZ hz
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,negOne,g,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
  ipra_simps
  linear_combination e

theorem reference_bound (R : PTm n) : Γ ⊢[PRAAx] bounded (reference : PTm n) (amplification R) one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ one _ one (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by unfold amplification; ipra_ring) (le_add_left one R))
    (GaussianRationalReciprocal.bounded_negative qone one one (le_refl one) GaussianRationalReciprocal.qone_bounded)

theorem sample_order_at (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (ap2 inputF p (referenceData R a b)))
      (fstT (ap2 inputF p (coefficientData z R B a b))) := by
  let s := GaussianBoundedConstantProductName.clock p (amplification R)
  let l := GaussianHarmonicLogarithmName.sample s a b
  have hr := (GaussianHarmonicLogarithmName.sample_real (Γ := Γ) s a b).andE₂
  have order := RationalArithmetic.multiply_monotone (fstT l) (fstT (reference : PTm n)) (fstT (coefficient z B))
    (GaussianEulerUpperPowerCoefficients.harmonic_sample_nonnegative s a b h.andE₂.andE₂.andE₂).andE₂
    (coefficient_lower z B h.andE₁.andE₁ h.andE₂.andE₁.andE₁)
  have left := (congrFst (GaussianBoundedConstantProductName.sample_at (Γ := Γ) GaussianHarmonicLogarithmName.nameF p
    (amplification R) (reference : PTm n) (GaussianHarmonicLogarithmName.data a b))).eqTrans
    ((GaussianPositiveExponentialProduct.real_product _ _ hr).eqTrans (RationalAlgebra.multiply_commutative _ _))
  have right := (congrFst (GaussianBoundedConstantProductName.sample_at (Γ := Γ) GaussianHarmonicLogarithmName.nameF p
    (amplification R) (coefficient z B) (GaussianHarmonicLogarithmName.data a b))).eqTrans
    ((GaussianPositiveExponentialProduct.real_product _ _ hr).eqTrans (RationalAlgebra.multiply_commutative _ _))
  exact RationalArgmin.rationalLE_congr left.eqSymm right.eqSymm order

theorem sample_order (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    sampleOrder inputF inputF (referenceData R a b) (coefficientData z R B a b) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [sampleOrder,Syn.shift,subst_referenceData,subst_coefficientData] using
    sample_order_at (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) hs

theorem ordered_exponentials (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    realOrder expF expF (referenceExpData R a b) (coefficientExpData z R B a b) :=
  GaussianSignedNameExponentialOrder.original_signed_name_order inputF inputF (radius R a) _ _
    (product_input _ _ _ _ h.andE₂.andE₂ (reference_bound R))
    (product_input _ _ _ _ h.andE₂.andE₂ (GaussianEulerIntegrandName.coefficient_bound z R B h.andE₁.andE₁ h.andE₁.andE₂))
    (product_real_samples _ _ _ _ (RationalGaussianEmbedding.axis_negative _ RationalGaussianEmbedding.axis_one))
    (product_real_samples _ _ _ _ (coefficient_axis z B h.andE₁.andE₁ h.andE₂.andE₁.andE₂))
    (sample_order z R B a b h)

theorem coefficient_input_cross (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent inputF powerExponentF (coefficientData z R B a b) (powerExponentData z B a b) := by
  let H := GaussianHarmonicLogarithmName.nameF
  let c := coefficient z B
  let X := GaussianHarmonicLogarithmName.data a b
  let Y := GaussianPositiveRationalLogarithm.data a b
  have first := GaussianBoundedConstantProductName.ordinary_product_identity H (amplification R) c X
    (.andI (GaussianHarmonicLogarithmName.name_regular a b h.andE₂.andE₂.andE₁)
      (GaussianEulerIntegrandName.coefficient_bound z R B h.andE₁.andE₁ h.andE₁.andE₂))
  have second := GaussianNameArithmetic.multiply_equivalent GaussianGammaCanonicalExponent.constantF GaussianGammaCanonicalExponent.constantF
    H GaussianPositiveRationalLogarithm.logF c c X Y
    (GaussianGammaCanonicalExponent.constant_regular c) (GaussianGammaCanonicalExponent.constant_regular c)
    (GaussianHarmonicLogarithmName.name_regular a b h.andE₂.andE₂.andE₁)
    (GaussianPositiveRationalLogarithm.name_regular a b h.andE₂.andE₂.andE₁)
    (GaussianNameEquivalence.diagonal_refl _ c)
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b h.andE₂.andE₂.andE₁)))
  exact cross_trans _ _ _ _ _ _ first second

theorem original_power_cross (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent expF powerF (coefficientExpData z R B a b) (powerData z B a b) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper inputF powerExponentF (radius R a) (powerRadius z B a b)
    (coefficientData z R B a b) (powerExponentData z B a b)
    (product_input _ _ _ _ h.andE₂.andE₂ (GaussianEulerIntegrandName.coefficient_bound z R B h.andE₁.andE₁ h.andE₁.andE₂))
    (GaussianEulerIntegrandName.power_input z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₂.andE₁))
    (coefficient_input_cross z R B a b h)

theorem reference_sample (p R a b : PTm n) : Γ ⊢[PRAAx]
    ap2 inputF p (referenceData R a b) ≐
      GaussianHarmonicLogarithmName.sample (GaussianBoundedConstantProductName.clock p (amplification R)) b a := by
  let s := GaussianBoundedConstantProductName.clock p (amplification R)
  let l := GaussianHarmonicLogarithmName.sample s a b
  have move := (GaussianEulerLowerRationalPowerReference.negative_move (Γ := Γ) qone l).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalMetric.qnegative_canonical l)))
  exact (GaussianBoundedConstantProductName.sample_at GaussianHarmonicLogarithmName.nameF p (amplification R)
    (reference : PTm n) (GaussianHarmonicLogarithmName.data a b)).eqTrans
      (move.eqTrans (GaussianEulerLowerPowerRebasing.reciprocal_sample s a b))

theorem reference_sample_error (p R a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b ⋏ le b a) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (ap2 inputF p (referenceData R a b))
      (ap2 GaussianHarmonicLogarithmName.nameF p (GaussianHarmonicLogarithmName.data b a)) two (unit p) := by
  have swapped : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source b a := .andI h.andE₁.andE₂ h.andE₁.andE₁
  let s := GaussianBoundedConstantProductName.clock p (amplification R)
  have e := GaussianEulerUpperPowerCompatibility.later_cross GaussianHarmonicLogarithmName.nameF GaussianHarmonicLogarithmName.nameF
    (GaussianHarmonicLogarithmName.data b a) (GaussianHarmonicLogarithmName.data b a)
    p s p (le_add_right _ _) (le_refl _)
    (GaussianNameEquivalence.cross_refl _ _ (GaussianHarmonicLogarithmName.name_regular _ _ swapped))
  exact GaussianRationalDistanceOrder.distance_congr (reference_sample p R a b).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) e

theorem reference_diagonal (R a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b ⋏ le b a) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal inputF GaussianHarmonicLogarithmName.nameF
      (referenceData R a b) (GaussianHarmonicLogarithmName.data b a) two := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (Syn.shift a) (Syn.shift b) ⋏ le (Syn.shift b) (Syn.shift a) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,subst_referenceData,GaussianHarmonicLogarithmName.subst_data,
    two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using reference_sample_error (var 0) (Syn.shift R) (Syn.shift a) (Syn.shift b) hs

theorem reference_input_cross (R a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b ⋏ le b a) : Γ ⊢[PRAAx]
    crossEquivalent inputF GaussianHarmonicLogarithmName.nameF (referenceData R a b) (GaussianHarmonicLogarithmName.data b a) := by
  have swapped : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source b a := .andI h.andE₁.andE₂ h.andE₁.andE₁
  exact GaussianNameRingLaws.equivalent_of_envelope inputF GaussianHarmonicLogarithmName.nameF
    (referenceData R a b) (GaussianHarmonicLogarithmName.data b a) two
    (product_input _ _ _ _ h (reference_bound R)).andE₁ (GaussianHarmonicLogarithmName.name_regular b a swapped)
    (reference_diagonal R a b h)

theorem reference_fraction (R a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b ⋏ le b a) : Γ ⊢[PRAAx]
    crossEquivalent expF GaussianGammaCanonicalExponent.constantF (referenceExpData R a b) (GaussianPositiveRationalLogarithm.fraction b a) := by
  have swapped : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source b a := .andI h.andE₁.andE₂ h.andE₁.andE₁
  have domain := GaussianHarmonicLogarithmPower.compact_domain b a swapped
  have target := GaussianHarmonicLogarithmName.common_input b a a b h.andE₁.andE₁ domain
  have proper := GaussianExponentialRadiusIndependence.independent_radii_proper inputF GaussianHarmonicLogarithmName.nameF
    (radius R a) (GaussianHarmonicLogarithmName.radius a b) (referenceData R a b) (GaussianHarmonicLogarithmName.data b a)
    (product_input _ _ _ _ h (reference_bound R)) target (reference_input_cross R a b h)
  exact cross_trans _ _ _ _ _ _ proper (GaussianHarmonicLogarithmName.original_exponential_fraction b a a b h.andE₁.andE₁ domain)

theorem original_power_order (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    realOrder GaussianGammaCanonicalExponent.constantF powerF (GaussianPositiveRationalLogarithm.fraction b a) (powerData z B a b) :=
  GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (reference_fraction R a b h.andE₂.andE₂)) (original_power_cross z R B a b h)
    (ordered_exponentials z R B a b h)

theorem reciprocal_lower_budget (p t z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack (fstT (GaussianPositiveRationalLogarithm.fraction b a))
      (fstT (ap2 powerF p (powerData z B a b))) one (unit p) one t := by
  have old := GaussianNamedPositiveExponentialOrder.real_order_at _ _ _ _ t p (original_power_order z R B a b h)
  exact RationalValueBounds.upper_congr
    (congrFst (GaussianGammaCanonicalExponent.constant_at t (GaussianPositiveRationalLogarithm.fraction b a)))
    (.eqRefl _) (by ipra_ring) (by ipra_ring) old

theorem original_reciprocal_lower (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (GaussianPositiveRationalLogarithm.fraction b a))
      (fstT (ap2 powerF p (powerData z B a b))) one (unit p) :=
  GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ one
    (reciprocal_lower_budget p (GaussianNamedRealOrderTransport.precision (fstT (GaussianPositiveRationalLogarithm.fraction b a))
      (fstT (ap2 powerF p (powerData z B a b))) (unit p) one) z R B a b h)

theorem reciprocal_at_least_half (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] le a (two*b)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction one two) (fstT (GaussianPositiveRationalLogarithm.fraction b a)) := by
  have rep := (GaussianRationalHorner.ofGaussian_represents (Γ := Γ) (scale b oneCode) a ha).andE₁
  have rep' : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (GaussianPositiveRationalLogarithm.fraction b a)) (ZT.ofNat b) a :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
      ring) (.eqRefl _) rep
  apply GaussianRationalMetric.comparison_of_cleared _ _ one b two a (le_succ_self one) ha
    (RationalIntegerNormalization.normalize_preserves_value _ _ (le_succ_self one)) rep'
  exact le_congr (by ipra_ring) (by ipra_ring) hab

/-- At every unchanged original observation on 1<=t<=2, the real power
is at least one half minus its own single dyadic observation error. -/
theorem original_half_lower (p z R B a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b) (hab : Γ ⊢[PRAAx] le a (two*b)) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (GaussianEuclideanDistanceName.fraction one two)
      (fstT (ap2 powerF p (powerData z B a b))) one (unit p) :=
  RationalValueBounds.upper_order_left _ _ _ _ _
    (reciprocal_at_least_half a b h.andE₂.andE₂.andE₁.andE₁ hab) (original_reciprocal_lower p z R B a b h)

theorem original_real_parameter_Euler_power_half_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 1) (var 2) (var 3) (var 4) (var 5) ⋏ le (var 4) (two*var 5)) ⟶
      RationalValueBounds.upper (GaussianEuclideanDistanceName.fraction one two)
        (fstT (ap2 powerF (var 0) (powerData (var 1) (var 3) (var 4) (var 5)))) one (unit (var 0))) :=
  closeUniv 6 (.impI (original_half_lower _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerRealPowerLowerOrder
