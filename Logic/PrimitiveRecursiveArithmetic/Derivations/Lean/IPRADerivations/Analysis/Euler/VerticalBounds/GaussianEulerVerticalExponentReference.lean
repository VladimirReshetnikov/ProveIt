import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalNativeProjection
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianBoundedConstantProductName
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerRealIntegrandNonnegative

/-!
# A shared-clock real projection of the original Euler exponent

Use one bounded constant-product clock for both original coefficients.
The actual real coordinates then agree exactly at every query. The real
native argument gives a canonical real sample, so the projected original
exponent is equivalent to the unchanged original real-argument exponent.
The original multiplication clocks are preserved through properness.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalExponentReference

open_ipra
open GaussianEulerVerticalNativeProjection (argument original_coefficient_projection)
open GaussianGammaRealValues (projection axisF axis_sample_at axis_regular projection_distance)
open GaussianEulerIntegrandName (coefficient decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (qadd qmul)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_to_diagonal)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev logarithmF : PR 2 := GaussianPositiveRationalLogarithm.logF
abbrev productF : PR 2 := GaussianBoundedConstantProductName.nameF logarithmF
def nameF : PR 2 := GaussianNameArithmetic.addF productF constantF
def productData (z R B a b : PTm n) : PTm n := GaussianBoundedConstantProductName.data
  (R+one) (coefficient z B) (GaussianPositiveRationalLogarithm.data a b)
def data (z R B a b : PTm n) : PTm n := GaussianNameArithmetic.addData (productData z R B a b) (decayPoint a b)
def clock (p R : PTm n) : PTm n := GaussianBoundedConstantProductName.clock (GaussianFastValueCut.exponent two p) (R+one)
def source (z R B a b : PTm n) : Fm PTm n := GaussianEulerUpperPowerCoefficients.source z R B ⋏ GaussianPositiveRationalLogarithm.source a b
ipra_subst productData
ipra_subst data
ipra_subst source

theorem product_input (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    GaussianBoundedConstantProductName.input logarithmF (R+one) (coefficient z B) (GaussianPositiveRationalLogarithm.data a b) :=
  .andI (GaussianPositiveRationalLogarithm.name_regular a b h.andE₂) (GaussianEulerIntegrandName.coefficient_bound z R B h.andE₁.andE₁ h.andE₁.andE₂)

theorem name_regular (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx] pointCN nameF (data z R B a b) :=
  GaussianNameArithmetic.add_fast _ _ _ _ (GaussianBoundedConstantProductName.name_regular _ _ _ _ (product_input z R B a b h)) (constant_regular _)

theorem sample_at (p z R B a b : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B a b) ≐ qadd (qmul (coefficient z B) (GaussianPositiveRationalLogarithm.sample (clock p R) a b)) (decayPoint a b) :=
  (GaussianNameArithmetic.add_at productF constantF _ _ p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qadd_congr
      (GaussianBoundedConstantProductName.sample_at logarithmF _ (R+one) (coefficient z B) (GaussianPositiveRationalLogarithm.data a b))
      (constant_at _ _))).eqTrans (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _)))

theorem original_cross (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianEulerIntegrandName.exponentF (data z R B a b) (GaussianEulerIntegrandName.exponentData z B a b) :=
  GaussianNameArithmetic.add_equivalent productF GaussianEulerIntegrandName.powerExponentF constantF constantF _ _ _ _
    (GaussianBoundedConstantProductName.name_regular _ _ _ _ (product_input z R B a b h))
    (GaussianEulerIntegrandName.power_exponent_regular z B a b (.andI h.andE₁.andE₁ h.andE₂))
    (constant_regular _) (constant_regular _)
    (cross_to_diagonal _ _ _ _ (GaussianBoundedConstantProductName.ordinary_product_identity _ _ _ _ (product_input z R B a b h)))
    (GaussianNameEquivalence.diagonal_refl _ _)

theorem coefficient_real_coordinate (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    fstT (coefficient z B) ≐ fstT (coefficient (argument z) B) := by
  have fixed : Γ ⊢[PRAAx] fstT (projection (coefficient z B)) ≐ fstT (coefficient z B) :=
    (fst_pair _ _).eqTrans (RationalNormalForm.normalize_fixed_point _ (GaussianRationalMetric.qsub_canonical _ _).andE₂.andE₁)
  exact fixed.eqSymm.eqTrans (congrFst (original_coefficient_projection z B hB))

theorem real_at (p z R B a b : PTm n) : Γ ⊢[PRAAx]
    fstT (ap2 nameF p (data z R B a b)) ≐
      RationalArithmetic.add (RationalArithmetic.multiply (fstT (coefficient z B))
        (fstT (GaussianPositiveRationalLogarithm.sample (clock p R) a b))) (fstT (decayPoint a b)) :=
  (congrFst (sample_at p z R B a b)).eqTrans ((RationalGaussianRealPart.real_add _ _).eqTrans
    (RationalAlgebra.add_congr (GaussianPositiveExponentialProduct.real_product _ _ (GaussianPositiveRationalLogarithm.sample_axis _ _ _)) (.eqRefl _)))

theorem sample_real_coordinate (p z R B a b : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    fstT (ap2 nameF p (data z R B a b)) ≐ fstT (ap2 nameF p (data (argument z) R B a b)) :=
  (real_at p z R B a b).eqTrans ((RationalAlgebra.add_congr
    (RationalAlgebra.multiply_congr (coefficient_real_coordinate z B hB) (.eqRefl _)) (.eqRefl _)).eqTrans
      (real_at p (argument z) R B a b).eqSymm)

theorem real_argument_axis (p z R B a b : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    RationalGaussianEmbedding.axis (ap2 nameF p (data (argument z) R B a b)) :=
  RationalGaussianEmbedding.axis_congr (sample_at p (argument z) R B a b).eqSymm
    (RationalGaussianEmbedding.axis_add _ _ (RationalGaussianEmbedding.axis_multiply _ _
      (GaussianEulerRealPowerLowerOrder.coefficient_axis (argument z) B hB (GaussianEulerVerticalNativeProjection.imaginary_zero z))
      (GaussianPositiveRationalLogarithm.sample_axis _ _ _)) (GaussianEulerRealIntegrandNonnegative.decay_point_axis a b hb))

theorem sample_projection (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    projection (ap2 nameF p (data z R B a b)) ≐ ap2 nameF p (data (argument z) R B a b) :=
  (RationalGaussianRealPart.embed_congr (sample_real_coordinate p z R B a b h.andE₁.andE₁)).eqTrans
    (RationalGaussianEmbedding.canonical_axis_roundtrip _ (GaussianNameArithmetic.add_canonical _ _ _ _ p)
      (real_argument_axis p z R B a b h.andE₁.andE₁ h.andE₂.andE₂))

theorem reference_projection (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent (axisF nameF) nameF (data z R B a b) (data (argument z) R B a b) := by
  have realSource : Γ ⊢[PRAAx] source (argument z) R B a b :=
    .andI (GaussianEulerVerticalNativeProjection.upper_source z R B h.andE₁) h.andE₂
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (axis_regular nameF _ (name_regular z R B a b h)) (name_regular (argument z) R B a b realSource)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,subst_data,GaussianEulerVerticalNativeProjection.subst_argument,Syn.shift] using
    (axis_sample_at nameF (var 0) (data (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b))).eqTrans
      (sample_projection (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) hs)

theorem projection_equivalent (F G : PR 2) (x y : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent F G x y) : Γ ⊢[PRAAx]
    crossEquivalent (axisF F) (axisF G) x y := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent F G (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  exact GaussianRationalDistanceOrder.distance_congr (axis_sample_at F _ _).eqSymm (axis_sample_at G _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (projection_distance _ _ _ _ (GaussianRationalHorner.positive_product _ _ (GaussianCoefficientNameBounds.unit_positive (var 1))
      (GaussianCoefficientNameBounds.unit_positive (var 0))) (GaussianNameEquivalence.cross_at _ _ _ _ (var 1) (var 0) hs))

theorem original_projected_exponent (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent (axisF GaussianEulerIntegrandName.exponentF) GaussianEulerIntegrandName.exponentF
      (GaussianEulerIntegrandName.exponentData z B a b) (GaussianEulerIntegrandName.exponentData (argument z) B a b) :=
  cross_trans _ _ _ _ _ _ (projection_equivalent _ _ _ _ (cross_symm _ _ _ _ (original_cross z R B a b h)))
    (cross_trans _ _ _ _ _ _ (reference_projection z R B a b h)
      (original_cross (argument z) R B a b (.andI (GaussianEulerVerticalNativeProjection.upper_source z R B h.andE₁) h.andE₂)))

theorem original_vertical_Euler_real_exponent_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      crossEquivalent (axisF GaussianEulerIntegrandName.exponentF) GaussianEulerIntegrandName.exponentF
        (GaussianEulerIntegrandName.exponentData (var 0) (var 2) (var 3) (var 4))
        (GaussianEulerIntegrandName.exponentData (argument (var 0)) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (original_projected_exponent _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalExponentReference
