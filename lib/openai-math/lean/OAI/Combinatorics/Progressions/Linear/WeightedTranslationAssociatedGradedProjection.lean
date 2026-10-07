import OAI.Combinatorics.Progressions.Fourier.HomogeneousGradedProjectionFrequency

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open Module MvPolynomial

variable {σ L ι : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s)
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra w d)
    (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration w d hwd).layer j)

noncomputable def weightedTranslationGradedProjection :
    F.AssociatedGraded →ₗ⁅ℚ⁆ weightedSubalgebra w d :=
  F.homogeneousGradedProjection (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem weightedTranslationGradedProjection_basis_base (i : ι) (a : σ) :
    (weightedTranslationGradedProjection F w d hw hwd φ hφ
      (F.associatedGradedBasis b ω hF i)).val.base a =
      if ω i = w a then (φ (b i)).val.base a else 0 := by
  simpa only [weightedTranslationGradedProjection, weightedBasis_repr_inl, weightedBasisGrade_inl] using
    F.homogeneousGradedProjection_basis_repr (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF i (Sum.inl a)

theorem weightedTranslationGradedProjection_basis_coeff (i : ι)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    (weightedTranslationGradedProjection F w d hw hwd φ hφ
      (F.associatedGradedBasis b ω hF i)).val.polynomial.coeff a.val =
      if ω i = d - Finsupp.weight w a.val then (φ (b i)).val.polynomial.coeff a.val else 0 := by
  simpa only [weightedTranslationGradedProjection, weightedBasis_repr_inr, weightedBasisGrade_inr] using
    F.homogeneousGradedProjection_basis_repr (weightedFiltration w d hwd)
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd)
      (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF i (Sum.inr a)

theorem weightedTranslationGradedProjection_image_graded
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule) :
    BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule :=
  F.homogeneousGradedProjection_image_graded (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF W hW

end Erdos3.PolynomialTranslationLie

end

end OAI
