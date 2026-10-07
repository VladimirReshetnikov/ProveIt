/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OAI.Combinatorics.Progressions.Dynamics.DetectedTranslationSeparationBudget
import OAI.Combinatorics.Progressions.Dynamics.RealProjectedPotentialGroupIdentity
import OAI.Combinatorics.Progressions.Dynamics.TranslationMajorSeparatedBudget
import OAI.Combinatorics.Progressions.Polynomial.HomogeneousScalarSymbolPolynomial
import OAI.Combinatorics.Progressions.Polynomial.TranslationMajorTwistedCorrelationStepDropPolynomial
import OAI.Combinatorics.Progressions.Polynomial.TranslationPolynomialSymbolLiftHom
import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialSubspaceSeparation
import OAI.Combinatorics.Progressions.Sampling.DetectedTranslationMajorSamplingContainment

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ L : Type} {U ι : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M) {e : ℕ}
    (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationSymbolProjection :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1) →*
      (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1) :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.polynomialSymbol_lowerCentralSeries_eq_bot (fun _ : U => 1))
    (hM := (weightedFiltration w d hwd).polynomialSymbol_lowerCentralSeries_eq_bot (fun _ : U => 1))
    ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.filteredPolynomialSymbolMap (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1))

@[simp] theorem detectedTranslationSymbolProjection_coord
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationSymbolProjection w d hw hwd M hM D P).coord =
      realificationLieHom
        ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.filteredPolynomialSymbolMap (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
          (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1)) P.coord := rfl

noncomputable def detectedTranslationSymbolLift :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1) →*
      (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  (translationPolynomialSymbolLiftHom w d hw hwd).comp
    (detectedTranslationSymbolProjection w d hw hwd M hM D)

@[simp] theorem detectedTranslationSymbolLift_apply
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationSymbolLift w d hw hwd M hM D P =
      translationPolynomialSymbolLift w d hw hwd
        (detectedTranslationSymbolProjection w d hw hwd M hM D P) := by
  simp only [detectedTranslationSymbolLift, MonoidHom.comp_apply,
    translationPolynomialSymbolLiftHom_apply]

@[simp] theorem detectedTranslationSymbolLift_log
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationSymbolLift w d hw hwd M hM D P).log =
      (weightedFiltration w d hwd).realSymbolRepresentative (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
        (realificationLieHom
          ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.filteredPolynomialSymbolMap (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
            (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1)) P.coord) := by
  rw [detectedTranslationSymbolLift_apply, translationPolynomialSymbolLift_log,
    detectedTranslationSymbolProjection_coord]

theorem detectedTranslationSymbolLift_mul
    (P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationSymbolLift w d hw hwd M hM D (P * Q) =
      detectedTranslationSymbolLift w d hw hwd M hM D P *
        detectedTranslationSymbolLift w d hw hwd M hM D Q :=
  (detectedTranslationSymbolLift w d hw hwd M hM D).map_mul P Q

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationSymbolProjection_pairOrbitSymbol
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) :
    detectedTranslationSymbolProjection w d hw hwd M hM D
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D p q b ω hN) = translationPolynomialSymbolHom w d hw hwd p := by
  apply NilpotentLieBCHGroup.ext
  rw [detectedTranslationSymbolProjection_coord, translationPolynomialSymbolHom_coord]
  exact pairOrbitSymbol_first_projection (weightedTranslationResidueNilmanifold w d hw hwd M hM) D (fun _ : U => 1) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) p q

theorem detectedTranslationSymbolLift_pairOrbitSymbol
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) :
    detectedTranslationSymbolLift w d hw hwd M hM D (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D p q b ω hN) =
      translationPolynomialSymbolLift w d hw hwd (translationPolynomialSymbolHom w d hw hwd p) := by
  rw [detectedTranslationSymbolLift_apply,
    detectedTranslationSymbolProjection_pairOrbitSymbol w d hw hwd M hM D b ω hN]

theorem detectedTranslationSymbolLift_value_mem_fast
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W)) (t : U → ℝ) :
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval (fun _ : U => 1) t
      (detectedTranslationSymbolLift w d hw hwd M hM D P)).coord ∈
      realificationLieSubalgebra
        (W.map (weightedTranslationGradedProjection (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))) := by
  change eval₂ t (detectedTranslationSymbolLift w d hw hwd M hM D P).log ∈ _
  rw [detectedTranslationSymbolLift_log]
  unfold weightedTranslationGradedProjection
  have h := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.projected_realSymbolRepresentative_mem_homogeneous_image (weightedFiltration w d hwd) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true) (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1) W P.coord hP t
  convert h using 1

theorem detectedTranslationSymbolLift_coefficients_mem_fast
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W)) (α : U →₀ ℕ) :
    coefficients (detectedTranslationSymbolLift w d hw hwd M hM D P).log α ∈
      realificationLieSubalgebra
        (W.map (weightedTranslationGradedProjection (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))) := by
  rw [detectedTranslationSymbolLift_log]
  unfold weightedTranslationGradedProjection
  have h := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.projected_realSymbolRepresentative_coefficients_mem_homogeneous_image (weightedFiltration w d hwd) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true) (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) (fun _ : U => 1) W P.coord hP α
  convert h using 1

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (v : σ → ℕ)

theorem realGradedSymbolPolynomial_constant (x : F.RealPolynomialSymbol v) :
    coefficients (F.realGradedSymbolPolynomial b ω hF v x) 0 = 0 := by
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  change ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
    (coefficients (F.realGradedSymbolPolynomial b ω hF v x) 0) i = 0
  apply F.realGradedSymbolPolynomial_coordinate_of_ne
  rw [map_zero]
  exact (F.adaptedBasis_weight_pos b ω hF i).ne

theorem scalarSymbolPolynomial_constant (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (g : F.RealPolynomialSymbolGroup v) :
    (F.scalarSymbolPolynomial b ω hF v θ g).coeff 0 = 0 := by
  rw [F.coeff_scalarSymbolPolynomial, F.realGradedSymbolPolynomial_constant, map_zero]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialTranslationLie

open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} {σ ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationBasePolynomial_constant
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup
      (fun _ : σ => 1)) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) 0 = 0 := by
  rw [detectedTranslationBasePolynomial_coefficients,
    NilpotentLieFiltration.realGradedSymbolPolynomial_constant, map_zero]

theorem detectedTranslationBaseFunctional_basis_eq_zero_of_ne
    (i : B) (j : ι) (hj : ω j ≠ w i) :
    detectedTranslationBaseFunctional w d hw hwd M hM D i
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis
        b ω hN j) = 0 := by
  rw [detectedTranslationBaseFunctional_basis_apply, ite_eq_right hj]

theorem detectedTranslationBaseScalar_isHomogeneous
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup
      (fun _ : σ => 1)) (i : B) :
    ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
      b ω hN (fun _ : σ => 1) (detectedTranslationBaseFunctional w d hw hwd M hM D i) g).IsHomogeneous (w i) := by
  exact NilpotentLieFiltration.scalarSymbolPolynomial_isWeightedHomogeneous
    _ b ω hN (fun _ : σ => 1) _ (w i)
    (fun j hj => detectedTranslationBaseFunctional_basis_eq_zero_of_ne
      w d hw hwd M hM D b ω hN i j hj) g

theorem detectedTranslationBasePolynomial_coordinate_isHomogeneous
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup
      (fun _ : σ => 1)) (i : B) :
    (coordinate (LinearMap.proj i : (B → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g)).IsHomogeneous (w i) := by
  rw [detectedTranslationBasePolynomial_coordinate]
  exact detectedTranslationBaseScalar_isHomogeneous w d hw hwd M hM D b ω hN g i

theorem detectedTranslationBasePolynomial_coefficients_apply_of_degree_ne
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup
      (fun _ : σ => 1)) (α : σ →₀ ℕ) (i : B) (hα : α.degree ≠ w i) :
    coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) α i = 0 := by
  rw [detectedTranslationBasePolynomial_coefficients_apply]
  exact (detectedTranslationBaseScalar_isHomogeneous w d hw hwd M hM D b ω hN g i).coeff_eq_zero hα

theorem detectedTranslationBasePolynomial_coordinate_totalDegree_le
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup
      (fun _ : σ => 1)) (i : B) :
    (coordinate (LinearMap.proj i : (B → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g)).totalDegree ≤ w i :=
  (detectedTranslationBasePolynomial_coordinate_isHomogeneous w d hw hwd M hM D b ω hN g i).totalDegree_le

theorem detectedTranslationBasePolynomial_coordinate_homogeneousComponent
    (g : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup
      (fun _ : σ => 1)) (i : B) :
    MvPolynomial.homogeneousComponent (w i)
      (coordinate (LinearMap.proj i : (B → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom
        (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g)) =
      coordinate (LinearMap.proj i : (B → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom
        (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN g) :=
  MvPolynomial.weightedHomogeneousComponent_eq_self
    (detectedTranslationBasePolynomial_coordinate_isHomogeneous w d hw hwd M hM D b ω hN g i)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationGroupEval (u : U → ℝ) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1) →*
      PolynomialTranslationGroupOver ℝ B :=
  (bchRealTranslationHom w d hwd).comp
    (((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u).comp (detectedTranslationSymbolLift w d hw hwd M hM D))

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationGroupEval_major_factorization
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : U => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (u : U → ℝ) :
    algebraicMajorSymbol
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F)
      (specializeMajorParameters (RingHom.id ℝ)
        (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F) 0)
      (majorTranslationTopCoordinates w A) u =
        detectedTranslationGroupEval w d hw hwd M hM D u E *
          detectedTranslationGroupEval w d hw hwd M hM D u P *
            detectedTranslationGroupEval w d hw hwd M hM D u Q := by
  rw [← majorTranslationPolynomialOrbit_degree_symbolLift_realEval w d hw hwd F hF A hA u,
    ← detectedTranslationSymbolLift_pairOrbitSymbol w d hw hwd M hM D b ω hN
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner,
    ← hprod]
  exact (detectedTranslationGroupEval w d hw hwd M hM D u).map_mul (E * P) Q |>.trans
    (congrArg (· * detectedTranslationGroupEval w d hw hwd M hM D u Q)
      ((detectedTranslationGroupEval w d hw hwd M hM D u).map_mul E P))

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationSymbolLift_base_coordinate
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) (i : B) :
    coordinate (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)).toAddMonoidHom
      (detectedTranslationSymbolLift w d hw hwd M hM D P).log =
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
      b ω hN (fun _ : U => 1) (detectedTranslationBaseFunctional w d hw hwd M hM D i) P := by
  rw [detectedTranslationSymbolLift_log]
  let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
  let η := (LinearMap.proj i).comp (baseLinear.comp (weightedSubalgebra w d).subtype)
  have h := N.filtration.homogeneousProjected_scalar_coordinate
    (weightedFiltration w d hwd) b ω hN
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    (fun _ : U => 1) η P.coord
  change N.filtration.scalarSymbolPolynomial b ω hN (fun _ : U => 1)
    (detectedTranslationBaseFunctional w d hw hwd M hM D i) P = _ at h
  dsimp only [η] at h
  rw [realifyTranslationBaseFunctional_eq_coord w d hw] at h
  convert h.symm using 1

theorem detectedTranslationGroupEval_base
    (u : U → ℝ)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    (detectedTranslationGroupEval w d hw hwd M hM D u P).base =
      eval₂ u (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P) := by
  funext i
  change (bchRealTranslationHom w d hwd
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval (fun _ : U => 1) u
      (detectedTranslationSymbolLift w d hw hwd M hM D P))).base i = _
  rw [bchRealTranslationHom_base_coordinate w d hw hwd]
  change ((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)
      (eval₂ u (detectedTranslationSymbolLift w d hw hwd M hM D P).log) =
    (LinearMap.proj i : (B → ℝ) →ₗ[ℝ] ℝ)
      (eval₂ u (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P))
  rw [coordinate_eval₂, coordinate_eval₂,
    detectedTranslationSymbolLift_base_coordinate w d hw hwd M hM D b ω hN,
    detectedTranslationBasePolynomial_coordinate w d hw hwd M hM D b ω hN]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationGroupEval_fast_potential
    (hd : 0 < d)
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (P : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W))
    (V : MvPolynomial B ℚ) :
    let fast := W.map (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))
    (∀ x ∈ fast, ∀ z ∈ fast.toSubmodule.map
      (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) →
    ∀ u z, z ∈ (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) →
    eval z (detectedTranslationGroupEval w d hw hwd M hM D u P).polynomial =
      eval₂ (algebraMap ℚ ℝ) z V -
        eval₂ (algebraMap ℚ ℝ) (z - (detectedTranslationGroupEval w d hw hwd M hM D u P).base) V := by
  intro fast hderiv u z hz
  have hg := detectedTranslationSymbolLift_value_mem_fast w d hw hwd M hM D b ω hN W P hP u
  have h := bchRealTranslationHom_eval_potential w d hw hd hwd fast V hderiv
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) u (detectedTranslationSymbolLift w d hw hwd M hM D P)) hg z hz
  simpa only [detectedTranslationGroupEval, MonoidHom.comp_apply, eval_map] using h

theorem detectedTranslationGroupEval_major_identity
    (hd : 0 < d)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : U => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W))
    (V : MvPolynomial B ℚ) :
    let fast := W.map (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))
    let K := (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
    let Ftop := weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F
    let F₀ := specializeMajorParameters (RingHom.id ℝ) Ftop 0
    (∀ x ∈ fast, ∀ z ∈ fast.toSubmodule.map
      (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) →
    (∀ u, (detectedTranslationGroupEval w d hw hwd M hM D u Q).base ∈ K) →
    ∀ u z, z ∈ K →
      let shift := z - fun j => eval u (majorTranslationTopCoordinates w A j)
      let left := detectedTranslationGroupEval w d hw hwd M hM D u E
      let right := detectedTranslationGroupEval w d hw hwd M hM D u Q
      eval (Sum.elim u z) Ftop = eval shift F₀ + eval (shift + left.base) left.polynomial -
        eval₂ (algebraMap ℚ ℝ) (shift + left.base) V + eval z right.polynomial +
          eval₂ (algebraMap ℚ ℝ) (z - right.base) V := by
  intro fast K Ftop F₀ hderiv hright u z hz shift left right
  have hfactor := detectedTranslationGroupEval_major_factorization w d hw hwd M hM D b ω hN
    F hF A hA partner E P Q hprod u
  have hpotential := detectedTranslationGroupEval_fast_potential w d hw hwd M hM D b ω hN
    hd W P hP V hderiv u
  have hid := PolynomialTranslationGroupOver.algebraic_major_eval_on_subspace K
    (specializeMajorParameters (RingHom.id ℝ) Ftop u) F₀ (map (algebraMap ℚ ℝ) V)
    (fun j => eval u (majorTranslationTopCoordinates w A j)) left
    (detectedTranslationGroupEval w d hw hwd M hM D u P) right hfactor
    (by simpa only [eval_map] using hpotential) (hright u) z hz
  simpa only [specializeMajorParameters_eval, eval₂_id, eval_map] using hid

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped Matrix

universe u v z

theorem exists_detectedTranslation_separated_base :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {B L : Type} {σ : Type u} {ι : Type v} {J : Type z}
    [Fintype B] [Fintype ι] [Fintype J] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (_hd : 1 ≤ d) {p : ℝ} (_hp : 0 ≤ p)
    (_hB : (Fintype.card B : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hJ : (Fintype.card J : ℝ) ≤ p)
    (_hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (W : LieSubalgebra ℚ
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (v : J → (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hvheight : ∀ j i, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hN).repr (v j) i) ≤ p)
    (E P Q X : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hprod : E * P * Q = X)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C)^C) ≤ T i)
    (_hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : σ => 1) T (Real.exp p) E)
    (_hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra
        b ω hN (fun _ : σ => 1) W))
    (m : ℕ) (_hm : 0 < m) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : σ => 1) m Q)
    (retained : Submodule ℝ (B → ℝ))
    (_hX : ∀ α, coefficients
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X) α ∈ retained)
    (_hretained : retained ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ)))),
    (∀ α, coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E) α ∈
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ)))) ∧
    (∀ α, coefficients (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q) α ∈
      Submodule.span ℝ (Set.range (fun j i =>
        (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ)))) ∧
    ∀ u : σ → ℝ,
      (detectedTranslationGroupEval w d hw hwd M hM D u E).base ∈
        Submodule.span ℝ (Set.range (fun j i =>
          (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) ∧
      (detectedTranslationGroupEval w d hw hwd M hM D u Q).base ∈
        Submodule.span ℝ (Set.range (fun j i =>
          (detectedTranslationBaseMap w d hw hwd M hM D (v j) i : ℝ))) := by
  let budget : Polynomial ℕ := (Polynomial.X + 3)^5
  obtain ⟨C, hC, hsep⟩ := exists_vectorPolynomial_subspace_separation budget
  refine ⟨C, hC, ?_⟩
  intro B L σ ι J _ _ _ _ _ w d hw hwd _ M hM e D b ω hN hd p hp hB hι hJ
    hb W v hv hvheight E P Q X hprod T hT hE hP m hm hmp hQ retained hX hretained
  have hbudget : budget.eval₂ (Nat.castRingHom ℝ) p = (p + 3)^5 := by
    simp [budget, Polynomial.eval₂_pow]
  obtain ⟨hpbudget, hsmall, hceil⟩ := detectedTranslationSeparation_budget hp
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  let H : ℕ := ⌈Real.exp ((p + 2)^4)⌉₊
  let A : Matrix B J ℚ := fun i j => detectedTranslationBaseMap w d hw hwd M hM D (v j) i
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    exact rationalHeightLE_ceil_exp
      (detectedTranslationBaseFunctional_value_logHeight w d hw hwd M hM D
        b ω hN hp hι hb (v j) (hvheight j) i)
  obtain ⟨q, hq, hqbound, hgrid⟩ :=
    detectedTranslationBasePolynomial_exists_coefficient_grid w d hw hwd M hM D
      b ω hN hp hι hb hB m hm hmp Q hQ
  have hslow := detectedTranslationBasePolynomial_slow_coefficients w d hw hwd M hM D
    b ω hN hp hι hb T hTpos E hE
  have hqbudget : (q : ℝ) ≤ Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) := by
    rw [hbudget]
    exact hqbound.trans (Real.exp_le_exp.mpr hsmall)
  obtain ⟨hEco, hQco, hEeval, hQeval⟩ :=
    hsep A H q (one_le_ceil_exp _) hq hA p hp
      (by rw [hbudget]; exact hB.trans hpbudget)
      (by rw [hbudget]; exact hJ.trans hpbudget)
      (by rw [hbudget]; exact hceil) hqbudget T hT
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN X)
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN E)
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN P)
      (detectedTranslationBasePolynomial w d hw hwd M hM D b ω hN Q)
      (detectedTranslationBasePolynomial_factorization w d hw hwd M hM D b ω hN hd E P Q X hprod)
      (fun α => hretained (hX α))
      (detectedTranslationBasePolynomial_fast_coefficients_mem_span w d hw hwd M hM D b ω hN W v hv P hP)
      (detectedTranslationBasePolynomial_constant w d hw hwd M hM D b ω hN E)
      (detectedTranslationBasePolynomial_constant w d hw hwd M hM D b ω hN Q)
      (fun α i => (hslow α i).trans (by
        rw [hbudget]
        exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hsmall)
          (monomialScale_pos T hTpos α).le)) hgrid
  refine ⟨hEco, hQco, fun u => ?_⟩
  rw [detectedTranslationGroupEval_base w d hw hwd M hM D b ω hN,
    detectedTranslationGroupEval_base w d hw hwd M hM D b ω hN]
  have heval (Y : VectorPolynomial σ ℝ (B → ℝ)) : eval₂ u Y = eval u Y := by
    simpa using (eval₂_algebraMap (S := ℝ) u Y)
  rw [heval, heval]
  exact ⟨hEeval u, hQeval u⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_separated_data
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      ∀ (retained : Fin d → Submodule ℝ (Fin m → ℝ)),
      (∀ h, HasLayerSamplingRank (h.val + 1) (fun i => (lengths i : ℝ))
        (Real.exp ((p + C)^C)) (retained h)
        (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i)))) →
      (∀ α, coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i))) α ∈
        ⨆ h, retained h) →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      let orbit := majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
        (fractionalCoefficientPolynomial_mem_weightedSupportLE F
          (Sum.elim (fun _ : U => 1) w) d hF) A hA
      let partner := D.raiseStepRealOrbit htd.le R.orbit
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C)^C) ∧
      ∃ (l : ℕ) (E P S : N.filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
        (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
        (v : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → N.filtration.AssociatedGraded)
        (Vfast : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial (Fin m) ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C)^C) ∧
        E * P * S = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          (D.raiseStep htd.le) orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1)
          (fun i => (lengths i : ℝ)) (Real.exp ((p + C)^C)) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l S ∧
        (∀ t : U → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
              (fun _ : U => 1)) P.coord)) ∈ realificationLieSubalgebra Vfast) ∧
        Vfast = W.map (weightedTranslationGradedProjection N.filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered
            (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))) ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (N.filtration.associatedGradedBasis b ω hLayers) ω W.toSubmodule ∧
        (∀ i j, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hLayers).repr (v i) j) ≤ (p+C)^C) ∧
        P.coord ∈ realificationLieSubalgebra
          (N.filtration.symbolPointwiseSubalgebra b ω hLayers (fun _ : U => 1) W) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ Vfast, ∀ z ∈ Vfast.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp ((p + C)^C) ∧
        (∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + C)^C)) ∧
        (∀ h, retained h ≤ (Vfast.toSubmodule.baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
        ∀ u : U → ℝ,
          (detectedTranslationGroupEval w d hw hwd M hM (D.raiseStep htd.le) u E).base ∈
            (Vfast.toSubmodule.baseChange ℝ).map
              (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) ∧
          (detectedTranslationGroupEval w d hw hwd M hM (D.raiseStep htd.le) u S).base ∈
            (Vfast.toSubmodule.baseChange ℝ).map
              (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) := by
  obtain ⟨a, ha, hdata⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_potential_data d hd
  obtain ⟨c, hc, hcontain⟩ := exists_majorTranslation_samplingRank_le_real_base_image
  obtain ⟨s, hs, hsep⟩ := exists_detectedTranslation_separated_base
  obtain ⟨C, hC, hbudget⟩ := exists_translationMajorSeparated_budget a c s
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
    retained hrank hAret N orbit partner
  let p₁ : ℝ := (p + a)^a
  have hp₁ : 0 ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).1
  have hpp₁ : p ≤ p₁ := (translationMajor_initial_budget_bounds a ha p hp).2.1
  obtain ⟨hb₁, hb₂, hb₃⟩ := hbudget p hp
  have hlarge₁ (i : U) : Real.exp ((p + a)^a) ≤ (lengths i : ℝ) :=
    (Real.exp_le_exp.mpr hb₁).trans (hlarge i)
  obtain ⟨b, ω, hLayers, hb, l, E, P, S, W, v, Vfast, V, q,
      hl, hlp, hprod, hE, hS, hfast, hVfast, hv, hW, hh, hP, hV,
      hderiv, hq, hqp, hgrid, hmass, hcoeff⟩ :=
    hdata w hw hwd M hM D htd Ψ F hF A hA K T hT hLip R p hp hgeometry hbound hR hRcap
      origin lengths hlengths hU hlarge₁ β hβ hcorr
  have hdim : (Fintype.card (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L))) : ℝ) ≤ p₁ := by
    simpa only [Fintype.card_fin] using
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).geometry_pair_finrank_le_budget
        (D.raiseStep htd.le) hgeometry (D.raiseStep_geometry htd.le hR.1) ha
  have hbase : (Fintype.card (Fin m) : ℝ) ≤ p₁ :=
    (weightedTranslationResidueNilmanifold_base_card_le w d hw hwd M hM hgeometry).trans hpp₁
  let Kfast := (Vfast.toSubmodule.baseChange ℝ).map
    (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
  have hspan : Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM (D.raiseStep htd.le) (v j) i : ℝ))) = Kfast := by
    dsimp only [Kfast]
    rw [hVfast]
    exact detectedTranslationBase_span_eq_real_image w d hw hwd M hM (D.raiseStep htd.le) W v hv
  have hTpos (i : U) : 0 < (lengths i : ℝ) := by exact_mod_cast hlengths i
  have hret : ∀ h, retained h ≤ Kfast := by
    intro h
    dsimp only [Kfast]
    rw [hVfast]
    apply hcontain w d hw hwd M hM (D.raiseStep htd.le) b ω hLayers hd hp₁ hbase hdim hdim
      hb W v hv hh (fractionalCoefficientPolynomial F)
      (fractionalCoefficientPolynomial_mem_weightedSupportLE F (Sum.elim (fun _ : U => 1) w) d hF)
      A hA partner E P S hprod (fun i => (lengths i : ℝ)) hTpos hE hP l hl hlp hS
      (h.val + 1) (Real.exp ((p + C)^C)) (retained h) (hrank h)
    exact Real.exp_le_exp.mpr hb₂
  let X := pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
    (D.raiseStep htd.le) orbit partner b ω hLayers
  have hX : ∀ α, coefficients
      (detectedTranslationBasePolynomial w d hw hwd M hM (D.raiseStep htd.le) b ω hLayers X) α ∈
        ⨆ h, retained h := by
    intro α
    rw [detectedTranslationBasePolynomial_majorOrbitSymbol w d hw hwd M hM (D.raiseStep htd.le)
      b ω hLayers (fractionalCoefficientPolynomial F)
      (fractionalCoefficientPolynomial_mem_weightedSupportLE F (Sum.elim (fun _ : U => 1) w) d hF)
      A hA partner]
    exact hAret α
  have hjoin : (⨆ h, retained h) ≤ Submodule.span ℝ (Set.range (fun j i =>
      (detectedTranslationBaseMap w d hw hwd M hM (D.raiseStep htd.le) (v j) i : ℝ))) := by
    rw [hspan]
    exact iSup_le hret
  obtain ⟨_, _, hgroup⟩ := hsep w d hw hwd M hM (D.raiseStep htd.le) b ω hLayers
    hd hp₁ hbase hdim hdim hb W v hv hh E P S X hprod (fun i => (lengths i : ℝ))
    (fun i => (Real.exp_le_exp.mpr hb₃).trans (hlarge i)) hE hP l hl hlp hS
    (⨆ h, retained h) hX hjoin
  have hexp := Real.exp_le_exp.mpr hb₁
  refine ⟨b, ω, hLayers, fun i j => (hb i j).trans hb₁, ?_⟩
  refine ⟨l, E, P, S, W, v, Vfast, V, q, hl, hlp.trans hexp, hprod, ?_⟩
  refine ⟨?_, hS, ?_⟩
  · exact N.filtration.symbolSlowBound_mono b ω hLayers (fun _ : U => 1)
      (fun i => (lengths i : ℝ)) hTpos hexp E hE
  refine ⟨?_, hVfast, hv, ?_⟩
  · convert hfast using 1
  refine ⟨hW, ?_, ?_, hV, hderiv, ?_⟩
  · exact fun i j => (hh i j).trans hb₁
  · convert hP using 1
  refine ⟨hq, hqp.trans hexp, hgrid, hmass.trans hexp, ?_, hret, ?_⟩
  · intro α
    exact ⟨(hcoeff α).1.trans hexp, (hcoeff α).2.trans hexp⟩
  · intro u
    have hu := hgroup u
    rw [hspan] at hu
    exact hu

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_degree_twisted_correlation_identity
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      ∀ (retained : Fin d → Submodule ℝ (Fin m → ℝ)),
      (∀ h, HasLayerSamplingRank (h.val + 1) (fun i => (lengths i : ℝ))
        (Real.exp ((p + C)^C)) (retained h)
        (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i)))) →
      (∀ α, coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin m))
          (fun i => weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i))) α ∈
        ⨆ h, retained h) →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      let orbit := majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
        (fractionalCoefficientPolynomial_mem_weightedSupportLE F
          (Sum.elim (fun _ : U => 1) w) d hF) A hA
      let partner := D.raiseStepRealOrbit htd.le R.orbit
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C)^C) ∧
      ∃ (l : ℕ) (E P S : N.filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
        (W : LieSubalgebra ℚ N.filtration.AssociatedGraded)
        (v : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → N.filtration.AssociatedGraded)
        (Vfast : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial (Fin m) ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C)^C) ∧
        E * P * S = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          (D.raiseStep htd.le) orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1)
          (fun i => (lengths i : ℝ)) (Real.exp ((p + C)^C)) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l S ∧
        (∀ t : U → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
              (fun _ : U => 1)) P.coord)) ∈ realificationLieSubalgebra Vfast) ∧
        Vfast = W.map (weightedTranslationGradedProjection N.filtration w d hw hwd
          (liePiEval (R := ℚ) true) (pairFirstProjection_filtered
            (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))) ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (N.filtration.associatedGradedBasis b ω hLayers) ω W.toSubmodule ∧
        (∀ i j, rationalLogHeight ((N.filtration.associatedGradedBasis b ω hLayers).repr (v i) j) ≤ (p+C)^C) ∧
        P.coord ∈ realificationLieSubalgebra
          (N.filtration.symbolPointwiseSubalgebra b ω hLayers (fun _ : U => 1) W) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ Vfast, ∀ z ∈ Vfast.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp ((p + C)^C) ∧
        (∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + C)^C)) ∧
        (∀ h, retained h ≤ (Vfast.toSubmodule.baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
        (∀ u : U → ℝ,
          (detectedTranslationGroupEval w d hw hwd M hM (D.raiseStep htd.le) u E).base ∈
            (Vfast.toSubmodule.baseChange ℝ).map
              (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) ∧
          (detectedTranslationGroupEval w d hw hwd M hM (D.raiseStep htd.le) u S).base ∈
            (Vfast.toSubmodule.baseChange ℝ).map
              (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) ∧
        ∀ (u : U → ℝ) (z : Fin m → ℝ),
          z ∈ (Vfast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype)) →
          let Ftop := weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d
            (fractionalCoefficientPolynomial F)
          let F₀ := specializeMajorParameters (RingHom.id ℝ) Ftop 0
          let shift := z - fun j => eval u (majorTranslationTopCoordinates w A j)
          let left := detectedTranslationGroupEval w d hw hwd M hM (D.raiseStep htd.le) u E
          let right := detectedTranslationGroupEval w d hw hwd M hM (D.raiseStep htd.le) u S
          eval (Sum.elim u z) Ftop =
            eval shift F₀ + eval (shift + left.base) left.polynomial -
              eval₂ (algebraMap ℚ ℝ) (shift + left.base) V + eval z right.polynomial +
                eval₂ (algebraMap ℚ ℝ) (z - right.base) V := by
  obtain ⟨C, hC, hdata⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_separated_data d hd
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
    retained hrank hAret N orbit partner
  obtain ⟨b, ω, hLayers, hb, l, E, P, S, W, v, Vfast, V, q,
      hl, hlp, hprod, hE, hS, hfast, hVfast, hv, hW, hh, hP, hV,
      hderiv, hq, hqp, hgrid, hmass, hcoeff, hret, hgroup⟩ :=
    hdata w hw hwd M hM D htd Ψ F hF A hA K T hT hLip R p hp hgeometry hbound hR hRcap
      origin lengths hlengths hU hlarge β hβ hcorr retained hrank hAret
  refine ⟨b, ω, hLayers, hb, ?_⟩
  refine ⟨l, E, P, S, W, v, Vfast, V, q, hl, hlp, hprod, hE, hS, ?_⟩
  refine ⟨?_, hVfast, hv, hW, hh, ?_⟩
  · convert hfast using 1
  refine ⟨?_, hV, hderiv, hq, hqp, hgrid, hmass, hcoeff, hret, hgroup, ?_⟩
  · convert hP using 1
  intro u z hz
  have hid := detectedTranslationGroupEval_major_identity w d hw hwd M hM (D.raiseStep htd.le)
    b ω hLayers hd (fractionalCoefficientPolynomial F)
    (fractionalCoefficientPolynomial_mem_weightedSupportLE F (Sum.elim (fun _ : U => 1) w) d hF)
    A hA partner E P S hprod W hP V
  dsimp only at hid
  rw [← hVfast] at hid
  exact hid hderiv (fun x => (hgroup x).2) u z hz

end Erdos3.PolynomialTranslationLie

end

end OAI
