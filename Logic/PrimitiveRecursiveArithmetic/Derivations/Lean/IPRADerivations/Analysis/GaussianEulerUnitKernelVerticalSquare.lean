import IPRADerivations.Analysis.GaussianEulerUnitSubstitutionKernel
import IPRADerivations.Analysis.GaussianEulerVerticalIntegrandSquare
import IPRADerivations.Analysis.GaussianEulerVerticalRealSamples

/-!
# Actual squared vertical identity for the original rational unit kernel

One bounded constant-product reference aligns the real coordinates of
the two original coefficients at one logarithm observation. Properness
returns both unchanged original multiplication and exponential programs.
The real comparator is the same original unit kernel at native Re z/B.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelVerticalSquare

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerVerticalNativeProjection (argument)
open GaussianEulerIntegrandName (coefficient)
open GaussianGammaRealValues (projection axisF axis_sample_at axis_regular)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianRationalHorner (qmul)
open GaussianEuclideanDistanceName (pointCN)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianExponentialRealPart (squareF squareData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev logarithmF : PR 2 := GaussianEulerUnitLogarithmicComposition.nameF
abbrev referenceF : PR 2 := GaussianBoundedConstantProductName.nameF logarithmF
def referenceData (z R B a b : PTm n) : PTm n := GaussianBoundedConstantProductName.data
  (R+one) (coefficient z B) (GaussianEulerUnitLogarithmicComposition.data a b)
def source (z R B a b : PTm n) : Fm PTm n :=
  GaussianEulerUpperPowerCoefficients.source z R B ⋏ GaussianEulerUnitLogarithmicMargin.source a b

@[simp] theorem subst_referenceData {m : ℕ} (σ : Fin n → PTm m) (z R B a b : PTm n) :
    Syn.subst σ (referenceData z R B a b) = referenceData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ b) := by simp [referenceData]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B a b : PTm n) :
    (source z R B a b).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ b) := by simp [source]

theorem kernel_source (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    GaussianEulerUnitSubstitutionKernel.source z B a b := .andI h.andE₁.andE₁ h.andE₂

theorem real_source (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    source (argument z) R B a b := .andI (GaussianEulerVerticalNativeProjection.upper_source z R B h.andE₁) h.andE₂

theorem logarithm_axis (p a b : PTm n) : Γ ⊢[PRAAx]
    RationalGaussianEmbedding.axis (GaussianEulerUnitLogarithmicComposition.sample p a b) :=
  RationalGaussianEmbedding.axis_congr (GaussianEulerUnitLogarithmicComposition.sample_at p a b).eqSymm
    (GaussianPositiveRationalLogarithm.sample_axis _ _ _)

theorem reference_input (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    GaussianBoundedConstantProductName.input logarithmF (R+one) (coefficient z B)
      (GaussianEulerUnitLogarithmicComposition.data a b) :=
  .andI (GaussianEulerUnitLogarithmicComposition.name_regular a b h.andE₂)
    (GaussianEulerIntegrandName.coefficient_bound z R B h.andE₁.andE₁ h.andE₁.andE₂)

theorem reference_regular (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    pointCN referenceF (referenceData z R B a b) :=
  GaussianBoundedConstantProductName.name_regular _ _ _ _ (reference_input z R B a b h)

theorem reference_at (p z R B a b : PTm n) : Γ ⊢[PRAAx]
    ap2 referenceF p (referenceData z R B a b) ≐ qmul (coefficient z B)
      (GaussianEulerUnitLogarithmicComposition.sample (GaussianBoundedConstantProductName.clock p (R+one)) a b) :=
  GaussianBoundedConstantProductName.sample_at _ _ _ _ _

theorem original_reference (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent referenceF GaussianEulerUnitSubstitutionKernel.exponentF
      (referenceData z R B a b) (GaussianEulerUnitSubstitutionKernel.exponentData z B a b) :=
  GaussianBoundedConstantProductName.ordinary_product_identity _ _ _ _ (reference_input z R B a b h)

theorem reference_projection_at (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    projection (ap2 referenceF p (referenceData z R B a b)) ≐ ap2 referenceF p (referenceData (argument z) R B a b) := by
  have coord : Γ ⊢[PRAAx] fstT (ap2 referenceF p (referenceData z R B a b)) ≐
      fstT (ap2 referenceF p (referenceData (argument z) R B a b)) :=
    (congrFst (reference_at p z R B a b)).eqTrans
      ((GaussianPositiveExponentialProduct.real_product _ _ (logarithm_axis _ a b)).eqTrans
        ((RationalAlgebra.multiply_congr
          (GaussianEulerVerticalExponentReference.coefficient_real_coordinate z B h.andE₁.andE₁) (.eqRefl _)).eqTrans
          ((GaussianPositiveExponentialProduct.real_product _ _ (logarithm_axis _ a b)).eqSymm.eqTrans
            (congrFst (reference_at p (argument z) R B a b)).eqSymm)))
  have ax : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis (ap2 referenceF p (referenceData (argument z) R B a b)) :=
    RationalGaussianEmbedding.axis_congr (reference_at p (argument z) R B a b).eqSymm
      (RationalGaussianEmbedding.axis_multiply _ _
        (GaussianEulerRealPowerLowerOrder.coefficient_axis (argument z) B h.andE₁.andE₁
          (GaussianEulerVerticalNativeProjection.imaginary_zero z)) (logarithm_axis _ a b))
  exact (RationalGaussianRealPart.embed_congr coord).eqTrans
    (RationalGaussianEmbedding.canonical_axis_roundtrip _ (by
      exact GaussianRationalHorner.canonical_congr (reference_at p (argument z) R B a b)
        (GaussianRationalHorner.qmul_canonical _ _)) ax)

theorem reference_projection (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent (axisF referenceF) referenceF (referenceData z R B a b) (referenceData (argument z) R B a b) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (axis_regular referenceF _ (reference_regular z R B a b h)) (reference_regular (argument z) R B a b (real_source z R B a b h))
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,subst_referenceData,GaussianEulerVerticalNativeProjection.subst_argument,Syn.shift] using
    (axis_sample_at referenceF (var 0) (referenceData (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b))).eqTrans
      (reference_projection_at (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift b) hs)

theorem original_projected_exponent (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent (axisF GaussianEulerUnitSubstitutionKernel.exponentF) GaussianEulerUnitSubstitutionKernel.exponentF
      (GaussianEulerUnitSubstitutionKernel.exponentData z B a b) (GaussianEulerUnitSubstitutionKernel.exponentData (argument z) B a b) :=
  cross_trans _ _ _ _ _ _
    (GaussianEulerVerticalExponentReference.projection_equivalent _ _ _ _ (cross_symm _ _ _ _ (original_reference z R B a b h)))
    (cross_trans _ _ _ _ _ _ (reference_projection z R B a b h) (original_reference (argument z) R B a b (real_source z R B a b h)))

theorem original_real_exponent_samples (z B a b : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    realSamples GaussianEulerUnitSubstitutionKernel.exponentF (GaussianEulerUnitSubstitutionKernel.exponentData (argument z) B a b) := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  refine .allI ?_
  have e := GaussianEulerUnitSubstitutionKernel.exponent_at (Γ := Γ.map Fm.shift) (var 0) (argument (Syn.shift z)) (Syn.shift B) (Syn.shift a) (Syn.shift b)
  have ca := GaussianRationalHorner.canonical_congr e (GaussianRationalHorner.qmul_canonical _ _)
  have ax := RationalGaussianEmbedding.axis_congr e.eqSymm (RationalGaussianEmbedding.axis_multiply _ _
    (GaussianEulerRealPowerLowerOrder.coefficient_axis (argument (Syn.shift z)) (Syn.shift B) bs (GaussianEulerVerticalNativeProjection.imaginary_zero _))
    (logarithm_axis _ (Syn.shift a) (Syn.shift b)))
  simpa only [realSamples,GaussianEulerUnitSubstitutionKernel.subst_exponentData,GaussianEulerVerticalNativeProjection.subst_argument,Syn.shift] using Prf.andI ca ax

theorem original_real_kernel_samples (z B a b : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    realSamples GaussianEulerUnitSubstitutionKernel.nameF (GaussianEulerUnitSubstitutionKernel.data (argument z) B a b) :=
  GaussianEulerVerticalRealSamples.original_exponential_real_samples _ _ _ (original_real_exponent_samples z B a b hB)

theorem original_real_kernel_nonnegative (p z B a b : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] GaussianEulerUnitLogarithmicMargin.source a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper RationalGaussianEmbedding.scalarZero
      (fstT (ap2 GaussianEulerUnitSubstitutionKernel.nameF p (GaussianEulerUnitSubstitutionKernel.data (argument z) B a b)))
      one (GaussianCoefficientNameBounds.unit p) :=
  GaussianRealNameExponentialNonnegative.original_observation_nonnegative _ _ _ p
    (GaussianEulerUnitSubstitutionKernel.exponential_input (argument z) B a b (.andI hB ht))
    (original_real_exponent_samples z B a b hB)

theorem original_kernel_square (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    crossEquivalent (squareF GaussianEulerUnitSubstitutionKernel.nameF) (squareF GaussianEulerUnitSubstitutionKernel.nameF)
      (squareData GaussianEulerUnitSubstitutionKernel.nameF (GaussianEulerUnitSubstitutionKernel.data z B a b))
      (squareData GaussianEulerUnitSubstitutionKernel.nameF (GaussianEulerUnitSubstitutionKernel.data (argument z) B a b)) := by
  let F := GaussianEulerUnitSubstitutionKernel.exponentF
  let x := GaussianEulerUnitSubstitutionKernel.exponentData z B a b
  let y := GaussianEulerUnitSubstitutionKernel.exponentData (argument z) B a b
  let Rz := GaussianEulerUnitSubstitutionKernel.radius z B a b
  let Ry := GaussianEulerUnitSubstitutionKernel.radius (argument z) B a b
  have input := GaussianEulerUnitSubstitutionKernel.exponential_input z B a b (kernel_source z R B a b h)
  have projected := GaussianEulerVerticalExponentialSquare.projected_input F Rz x input
  have other := GaussianEulerUnitSubstitutionKernel.exponential_input (argument z) B a b (kernel_source _ _ _ _ _ (real_source z R B a b h))
  have proper := GaussianExponentialRadiusIndependence.independent_radii_proper (axisF F) F Rz Ry x y projected other
    (original_projected_exponent z R B a b h)
  have squared := GaussianEulerVerticalIntegrandSquare.square_equivalent (GaussianRadiusExponentialName.nameF (axisF F))
    GaussianEulerUnitSubstitutionKernel.nameF (GaussianRadiusExponentialName.data Rz x) (GaussianEulerUnitSubstitutionKernel.data (argument z) B a b)
    (GaussianRadiusExponentialName.name_regular _ _ _ projected) (GaussianEulerUnitSubstitutionKernel.name_regular _ _ _ _ (kernel_source _ _ _ _ _ (real_source z R B a b h))) proper
  exact cross_trans _ _ _ _ _ _ (GaussianEulerVerticalExponentialSquare.actual_exponential_square_projection F Rz x input) squared

theorem actual_original_unit_kernel_vertical_square_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      crossEquivalent (squareF GaussianEulerUnitSubstitutionKernel.nameF) (squareF GaussianEulerUnitSubstitutionKernel.nameF)
        (squareData GaussianEulerUnitSubstitutionKernel.nameF (GaussianEulerUnitSubstitutionKernel.data (var 0) (var 2) (var 3) (var 4)))
        (squareData GaussianEulerUnitSubstitutionKernel.nameF (GaussianEulerUnitSubstitutionKernel.data (argument (var 0)) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (original_kernel_square _ _ _ _ _ Prf.hyp0))

theorem actual_original_real_unit_kernel_nonnegative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 2) ⋏ GaussianEulerUnitLogarithmicMargin.source (var 3) (var 4)) ⟶
      RationalValueBounds.upper RationalGaussianEmbedding.scalarZero
        (fstT (ap2 GaussianEulerUnitSubstitutionKernel.nameF (var 0) (GaussianEulerUnitSubstitutionKernel.data (argument (var 1)) (var 2) (var 3) (var 4))))
        one (GaussianCoefficientNameBounds.unit (var 0))) :=
  closeUniv 5 (.impI (original_real_kernel_nonnegative _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelVerticalSquare
