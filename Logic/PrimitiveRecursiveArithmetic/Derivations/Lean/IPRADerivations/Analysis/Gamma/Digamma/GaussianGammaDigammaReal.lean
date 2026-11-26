import IPRADerivations.Analysis.Gamma.Digamma.Comparison.GaussianGammaDigammaDerivativeProductOrder

/-!
# Real representatives of the original positive rational digamma

Real observations of the Gamma divided difference approximate the
first logarithmic Euler integral. This identifies its real-axis
projection with the original derivative name and exports an exact
real representative of the original digamma.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaReal

open_ipra
open ComplexLogarithmRemainder (oneCode scale re im)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaDigammaNative (derivativeData derivative_regular reciprocalData reciprocal_regular minimumDenominator)
open GaussianGammaDigammaDerivativeProductOrder (rawSlope quotientCost raw_slope_near natural_inverse)
open GaussianGammaDigammaStep (neighborData neighborNumerator neighborDenominator neighbor_source)
open GaussianGammaRealValues (axisF projection axis_sample_at axis_regular)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm)
open GaussianNamedDifference (difference_distance)
open GaussianNamedDifferenceQuotient (inverse scale_distance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul positive_product canonical)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingGammaLogarithm (arg source gammaData gamma_source gammaRetimedF gammaRetimedData gamma_retimed_cross log_input)
open RationalGaussianEmbedding (axis axis_add axis_multiply axis_negative)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "CF" => GaussianGammaC7Name.nameF
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "GF" => gammaRetimedF
local notation "gg" => gammaRetimedData

def nameF : PR 2 := multiplyF (axisF CF) (axisF IF)
def data (a b : PTm n) : PTm n := multiplyData (axisF CF) (axisF IF) (reciprocalData a b) (derivativeData a b)

ipra_subst data

def realSlope (t a b D : PTm n) : PTm n :=
  qmul (naturalPoint D) (qsub
    (ap2 GF t (gg (neighborNumerator a b D) (neighborDenominator b D))) (ap2 GF t (gg a b)))

theorem real_slope_real (t a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] canonical (realSlope t a b D) ⋏ axis (realSlope t a b D) := by
  have a₁ := (GaussianNamedPositiveLogarithm.admissible_at _ t _ _ _
    (log_input _ _ (neighbor_source a b D hs hD))).andE₂.andE₁
  have a₂ := (GaussianNamedPositiveLogarithm.admissible_at _ t _ _ _ (log_input a b hs)).andE₂.andE₁
  exact .andI (GaussianRationalHorner.qmul_canonical _ _)
    (axis_multiply _ _ (GaussianStirlingNames.fraction_axis D one (le_refl one)) (axis_add _ _ a₁ (axis_negative _ a₂)))

private theorem real_slope_error (t a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded (rawSlope t a b D) (realSlope t a b D) (num 4*D) (unit t) := by
  let e := neighborNumerator a b D
  let d := neighborDenominator b D
  have hp := unit_positive (Γ := Γ) t
  have ha := cross_at _ _ _ _ t t (gamma_retimed_cross _ _ (neighbor_source a b D hs hD))
  have hb := cross_at _ _ _ _ t t (gamma_retimed_cross a b hs)
  have convert := fun (x y : PTm n) (h : Γ ⊢[PRAAx] distanceBounded x y (unit t+unit t) (unit t*unit t)) =>
    distance_radius_mono x y _ _ two (unit t) (positive_product _ _ hp hp) hp
      (le_of_eq_add (d := zero) (by ipra_ring)) h
  have diff := difference_distance (ap2 gammaF t (neighborData a b D)) (ap2 GF t (gg e d))
    (ap2 gammaF t (gammaData a b)) (ap2 GF t (gg a b)) two two (unit t) hp (convert _ _ ha) (convert _ _ hb)
  have inv := GaussianNamedDifferenceQuotient.inverse_bound oneCode D
    (GaussianGammaUnitInverseSamples.actual_step_separated D hD)
  exact distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (natural_inverse D hD) (.eqRefl _))
    (by ipra_ring) (.eqRefl _) (scale_distance (inverse oneCode D) _ _ D _ _ hp inv diff)

set_option maxHeartbeats 800000 in
theorem derivative_projection_error (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 IF p (derivativeData a b)) (ap2 (axisF IF) p (derivativeData a b))
      (num 10) (unit p) := by
  let D := minimumDenominator p a b
  let L := (one+quotientCost a b D)+num 4*D
  let t := GaussianFastValueCut.exponent L p
  let x := derivativeData a b
  let y := ap2 IF p x
  let r := realSlope t a b D
  have hp := unit_positive (Γ := Γ) p
  have ht := unit_positive (Γ := Γ) t
  have hd : Γ ⊢[PRAAx] le one D := GaussianGammaDigammaStep.denominator_positive p a b D (le_refl _)
  have late (A : PTm n) (h : Γ ⊢[PRAAx] le A L) : Γ ⊢[PRAAx] le (A*unit p) (unit t) :=
    le_trans (mul_le_mul_right _ h) (GaussianFastValueCut.query_budget _ _)
  have hP := le_congr (one_mul _) (.eqRefl _)
    (late one (le_trans (le_add_right _ _) (le_add_right _ _)))
  have hQ := late (quotientCost a b D) (le_trans (le_add_left _ _) (le_add_right _ _))
  have hR := late (num 4*D) (le_add_left _ _)
  have left := distance_symmetric _ _ _ _ hp (raw_slope_near p t a b D hs (le_refl _) hP hQ)
  have right := distance_radius_mono _ _ _ _ one (unit p) ht hp
    (le_congr (.eqRefl _) (one_mul _).eqSymm hR) (real_slope_error t a b D hs hd)
  have near : Γ ⊢[PRAAx] distanceBounded y r (num 5) (unit p) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hp left right)
  have hr := real_slope_real t a b D hs hd
  have e : Γ ⊢[PRAAx] projection r ≐ r :=
    RationalGaussianEmbedding.canonical_axis_roundtrip _ hr.andE₁ hr.andE₂
  have projected := distance_congr (.eqRefl _) e (.eqRefl _) (.eqRefl _)
    (GaussianGammaRealValues.projection_distance _ _ _ _ hp near)
  exact distance_congr (.eqRefl _) (axis_sample_at IF p x).eqSymm (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp near (distance_symmetric _ _ _ _ hp projected))

theorem derivative_cross (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent IF (axisF IF) (derivativeData a b) (derivativeData a b) := by
  have h := derivative_regular a b hs
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 10) h (axis_regular _ _ h) (.allI ?_)
  have hs' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift,Syn.shift,GaussianStirlingGammaLogarithm.subst_source] using hs.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,GaussianGammaDigammaNative.subst_derivativeData,PTm.subst_num] using
    derivative_projection_error (var 0) (Syn.shift a) (Syn.shift b) hs'

private theorem argument_fixed (r : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalReciprocal.conjugate (arg r) ≐ arg r := by
  let u := ZT.ofNat r*re oneCode
  let v := ZT.ofNat r*im oneCode
  let a := pairT u.pos u.neg
  let b := pairT v.pos v.neg
  let z := arg r
  have p : Γ ⊢[PRAAx] fstT z ≐ a := fst_pair _ _
  have q : Γ ⊢[PRAAx] sndT z ≐ b := snd_pair _ _
  have iv : ZT.toZ Γ v = 0 := by
    simp [v,ZT.toZ_mul,GaussianRootAlgebra.im_one,ZT.toZ_ofNat]
  have e : Γ ⊢[PRAAx] v.pos ≐ v.neg := by
    apply deriveNat
    unfold ZT.toZ at iv
    linear_combination iv
  change Γ ⊢[PRAAx] pairT (pairT (fstT (fstT z)) (sndT (fstT z)))
    (pairT (sndT (sndT z)) (fstT (sndT z))) ≐ pairT a b
  exact congrPairT
    (congrPairT ((congrFst p).eqTrans (fst_pair _ _)) ((congrSnd p).eqTrans (snd_pair _ _)))
    (congrPairT ((congrSnd q).eqTrans ((snd_pair _ _).eqTrans e.eqSymm))
      ((congrFst q).eqTrans ((fst_pair _ _).eqTrans e)))

theorem reciprocal_cross (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent CF (axisF CF) (reciprocalData a b) (reciprocalData a b) :=
  GaussianGammaRealValues.original_reciprocal_real (arg a) a b (gamma_source a b hs).andE₁ (argument_fixed a)

theorem name_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN nameF (data a b) :=
  multiply_fast _ _ _ _ (axis_regular _ _ (reciprocal_regular _ _ hs)) (axis_regular _ _ (derivative_regular _ _ hs))

theorem name_real (a b : PTm n) : Γ ⊢[PRAAx] realSamples nameF (data a b) :=
  GaussianStirlingNames.multiply_real _ _ _ _ (GaussianEulerVerticalProjection.projected_real_samples _ _)
    (GaussianEulerVerticalProjection.projected_real_samples _ _)

theorem original_cross (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent DF nameF (GaussianGammaDigammaNative.data a b) (data a b) :=
  GaussianGammaAdjacentCutoff.multiply_cross CF (axisF CF) IF (axisF IF) _ _ _ _
    (reciprocal_regular _ _ hs) (axis_regular _ _ (reciprocal_regular _ _ hs))
    (derivative_regular _ _ hs) (axis_regular _ _ (derivative_regular _ _ hs))
    (reciprocal_cross a b hs) (derivative_cross a b hs)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaReal
