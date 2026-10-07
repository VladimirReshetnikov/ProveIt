import OAI.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotential
import OAI.Combinatorics.Progressions.Polynomial.DetectedTranslationBasePolynomialBounds

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

section General

variable {B ι J L : Type*} [Fintype B] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s)
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (φ : L →ₗ⁅ℚ⁆ weightedSubalgebra w d)
    (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ (weightedFiltration w d hwd).layer j)

noncomputable def detectedTranslationProjectedGenerators (v : J → F.AssociatedGraded) :
    J → weightedSubalgebra w d :=
  fun j => weightedTranslationGradedProjection F w d hw hwd φ hφ (v j)

noncomputable def detectedTranslationProjectedBaseMatrix (v : J → F.AssociatedGraded) :
    Matrix B J ℚ :=
  fun i j => (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).val.base i

theorem detectedTranslationProjectedGenerators_span
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v)) =
      (W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule :=
  F.homogeneousGradedProjection_span (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ W v hv

theorem detectedTranslationProjectedBaseMatrix_span
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (fun j i => detectedTranslationProjectedBaseMatrix F w d hw hwd φ hφ v i j)) =
      (W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule.map
        (baseLinear.comp (weightedSubalgebra w d).subtype) :=
  (coordinateImage_eq_span _ _ (detectedTranslationProjectedGenerators_span F w d hw hwd φ hφ W v hv)
    (baseLinear.comp (weightedSubalgebra w d).subtype)).symm

theorem detectedTranslationProjectedBaseMatrix_real_image_eq_span
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    ((W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) =
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationProjectedBaseMatrix F w d hw hwd φ hφ v i j : ℝ))) :=
  realifyCoordinateMap_image_eq_span _ _
    (detectedTranslationProjectedGenerators_span F w d hw hwd φ hφ W v hv)
    (baseLinear.comp (weightedSubalgebra w d).subtype)

theorem detectedTranslationProjectedBaseMatrix_real_mem_span
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {x : ℝ ⊗[ℚ] weightedSubalgebra w d}
    (hx : x ∈ (W.map (weightedTranslationGradedProjection F w d hw hwd φ hφ)).toSubmodule.baseChange ℝ) :
    realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype) x ∈
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationProjectedBaseMatrix F w d hw hwd φ hφ v i j : ℝ))) :=
  realifyCoordinateMap_mem_span _ _ (detectedTranslationProjectedGenerators_span F w d hw hwd φ hφ W v hv)
    (baseLinear.comp (weightedSubalgebra w d).subtype) hx

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p)
    (v : J → F.AssociatedGraded)
    (hcoords : ∀ j i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v j) i) ≤ p)

include b ω hF hp hι hentries hcoords

theorem detectedTranslationProjectedGenerators_coordinate_logHeight (j : J) (i : WeightedBasisIndex w d) :
    rationalLogHeight ((weightedBasis w d hw).repr
      (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j) i) ≤ (p + 2)^4 :=
  F.homogeneousGradedProjection_coordinate_logHeight (weightedFiltration w d hwd)
    (weightedBasis w d hw) (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) φ hφ b ω hF hp hι hentries (v j) (hcoords j) i

theorem detectedTranslationProjectedBaseMatrix_logHeight (i : B) (j : J) :
    rationalLogHeight (detectedTranslationProjectedBaseMatrix F w d hw hwd φ hφ v i j) ≤ (p + 2)^4 :=
  detectedTranslationProjectedGenerators_coordinate_logHeight F w d hw hwd φ hφ b ω hF
    hp hι hentries v hcoords j (Sum.inl i)

theorem detectedTranslationProjectedGenerators_polynomial_logHeight (j : J) (a : B →₀ ℕ) :
    rationalLogHeight
      ((detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).val.polynomial.coeff a) ≤ (p + 2)^4 := by
  by_cases ha : Finsupp.weight w a < d
  · exact detectedTranslationProjectedGenerators_coordinate_logHeight F w d hw hwd φ hφ b ω hF
      hp hι hentries v hcoords j (Sum.inr ⟨a, ha⟩)
  · have hz : (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).val.polynomial.coeff a = 0 := by
      by_contra hne
      have hh := (detectedTranslationProjectedGenerators F w d hw hwd φ hφ v j).property.2
        (MvPolynomial.mem_support_iff.mpr hne)
      change Finsupp.weight w a + 1 ≤ d at hh
      omega
    rw [hz]
    simp only [rationalLogHeight, Rat.num_zero, Int.natAbs_zero, Nat.cast_zero,
      Rat.den_zero, Nat.cast_one, max_eq_right (zero_le_one : (0 : ℝ) ≤ 1), Real.log_one]
    positivity

end General

theorem residuePairProjectedGenerators_data
    {B L ι : Type} [Fintype B] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e) :
    let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    ∀ (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
      (hN : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
      {n : ℕ} (v : Fin n → N.filtration.AssociatedGraded),
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
      ∀ {p : ℝ}, 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ p) →
      (∀ j i, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p) →
      let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d := liePiEval true
      let hφ := pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      let U := W.map (weightedTranslationGradedProjection N.filtration w d hw hwd φ hφ)
      let g := detectedTranslationProjectedGenerators N.filtration w d hw hwd φ hφ v
      let C := detectedTranslationProjectedBaseMatrix N.filtration w d hw hwd φ hφ v
      Submodule.span ℚ (Set.range g) = U.toSubmodule ∧
      Submodule.span ℚ (Set.range (fun j i => C i j)) =
        U.toSubmodule.map (baseLinear.comp (weightedSubalgebra w d).subtype) ∧
      (∀ j i, rationalLogHeight ((weightedBasis w d hw).repr (g j) i) ≤ (p + 2)^4) ∧
      (∀ i j, rationalLogHeight (C i j) ≤ (p + 2)^4) ∧
      ∀ j a, rationalLogHeight ((g j).val.polynomial.coeff a) ≤ (p + 2)^4 := by
  intro N b ω hN W n v hv p hp hι hb hcoords φ hφ U g C
  have hentries (i : ι) (j : WeightedBasisIndex w d) :
      rationalLogHeight ((weightedBasis w d hw).repr (φ (b i)) j) ≤ p := by
    have h := productProjection_coordinate_logHeight
      (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      (b i) (hb i) true (weightedIndexOrder w d j)
    change rationalLogHeight ((weightedOrderedBasis w d hw).repr (φ (b i))
      (weightedIndexOrder w d j)) ≤ p at h
    have he := weightedOrderedBasis_repr w d hw (φ (b i)) (weightedIndexOrder w d j)
    have he' : (weightedOrderedBasis w d hw).repr (φ (b i)) (weightedIndexOrder w d j) =
        (weightedBasis w d hw).repr (φ (b i)) j :=
      he.trans (congrArg ((weightedBasis w d hw).repr (φ (b i)))
        ((weightedIndexOrder w d).symm_apply_apply j))
    exact he' ▸ h
  exact ⟨detectedTranslationProjectedGenerators_span N.filtration w d hw hwd φ hφ W v hv,
    detectedTranslationProjectedBaseMatrix_span N.filtration w d hw hwd φ hφ W v hv,
    detectedTranslationProjectedGenerators_coordinate_logHeight N.filtration w d hw hwd φ hφ
      b ω hN hp hι hentries v hcoords,
    detectedTranslationProjectedBaseMatrix_logHeight N.filtration w d hw hwd φ hφ
      b ω hN hp hι hentries v hcoords,
    detectedTranslationProjectedGenerators_polynomial_logHeight N.filtration w d hw hwd φ hφ
      b ω hN hp hι hentries v hcoords⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {B L σ ι : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

 theorem detectedTranslationBasePolynomial_majorOrbitSymbol
    (F : MvPolynomial (σ ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : σ => 1) w) d)
    (A : B → MvPolynomial σ ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (q : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1)) :
    detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) q b ω hN) =
      ofCoordinates (R := ℝ) (Pi.basisFun ℝ B)
        (fun i => weightedHomogeneousComponent (fun _ : σ => 1) (w i) (A i)) := by
  apply (coordinatesEquiv (R := ℝ) (Pi.basisFun ℝ B)).injective
  funext i
  change coordinate ((Pi.basisFun ℝ B).coord i).toAddMonoidHom _ =
    coordinate ((Pi.basisFun ℝ B).coord i).toAddMonoidHom
      (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B)
        (fun j => weightedHomogeneousComponent (fun _ : σ => 1) (w j) (A j)))
  rw [coordinate_ofCoordinates]
  exact (detectedTranslationBasePolynomial_coordinate w d hw hwd M hM D b ω hN _ i).trans
    (detectedTranslationBaseFunctional_majorOrbitSymbol w d hw hwd M hM D b ω hN F hF A hA q i)

 theorem detectedTranslationBase_span_eq_real_image {J : Type*}
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) =
      (((W.map (weightedTranslationGradedProjection
        (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))).toSubmodule).baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) := by
  exact (detectedTranslationProjectedBaseMatrix_real_image_eq_span
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
    w d hw hwd (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) W v hv).symm

end Erdos3.PolynomialTranslationLie

end

end OAI
