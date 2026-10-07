/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Geometry.DetectedTranslationCoordinateBudget
import OAI.Combinatorics.Progressions.Geometry.MajorTranslationBaseCoordinates
import OAI.Combinatorics.Progressions.Linear.NativePairSymbolProjection
import OAI.Combinatorics.Progressions.Linear.WeightedTranslationAssociatedGradedProjection
import OAI.Combinatorics.Progressions.Sampling.ScalarSymbolFamilyCoefficientGrid

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (w : σ → ℕ)

theorem realSymbolRepresentative_eq_homogeneous_map (x : F.RealPolynomialSymbol w) :
    F.realSymbolRepresentative b ω hF w x =
      VectorPolynomial.map
        ((realificationLieHom (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom).toLinearMap.restrictScalars ℚ)
        (F.realGradedSymbolPolynomial b ω hF w x) :=
  F.realSymbolRepresentative_eq_map b ω hF w x

theorem realSymbolRepresentative_homogeneous_coefficient (x : F.RealPolynomialSymbol w)
    (α : σ →₀ ℕ) :
    coefficients (F.realSymbolRepresentative b ω hF w x) α =
      realificationLieHom (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom
        (coefficients (F.realGradedSymbolPolynomial b ω hF w x) α) :=
  F.realSymbolRepresentative_coefficient_splitting b ω hF w x α

theorem realSymbolRepresentative_homogeneous_eval (x : F.RealPolynomialSymbol w)
    (t : σ → ℝ) :
    eval₂ t (F.realSymbolRepresentative b ω hF w x) =
      realificationLieHom (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom
        (eval₂ t (F.realGradedSymbolPolynomial b ω hF w x)) :=
  F.realSymbolRepresentative_eval₂ b ω hF w x t

theorem realSymbolRepresentative_mem_homogeneous_image
    (W : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W))
    (t : σ → ℝ) :
    eval₂ t (F.realSymbolRepresentative b ω hF w x) ∈
      realificationLieSubalgebra (W.map (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom) := by
  rw [F.realSymbolRepresentative_homogeneous_eval b ω hF hb w x t,
    realificationLieSubalgebra_map]
  exact ⟨_, (F.mem_real_symbolPointwiseSubalgebra_iff_values b ω hF w W x).mp hx t, rfl⟩

theorem realSymbolRepresentative_coefficients_mem_homogeneous_image
    (W : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W))
    (α : σ →₀ ℕ) :
    coefficients (F.realSymbolRepresentative b ω hF w x) α ∈
      realificationLieSubalgebra (W.map (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom) := by
  rw [F.realSymbolRepresentative_homogeneous_coefficient b ω hF hb w x α,
    realificationLieSubalgebra_map]
  exact ⟨_, (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients b ω hF w W x).mp hx α, rfl⟩

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialTranslationLie

open Module VectorPolynomial
open scoped TensorProduct

variable {B U : Type*} [Fintype B]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)

theorem weightedSymbolRepresentative_mem_associatedGraded_image
    (v : U → ℕ) (W : LieSubalgebra ℚ (weightedFiltration w d hwd).AssociatedGraded)
    (x : (weightedFiltration w d hwd).RealPolynomialSymbol v)
    (hx : x ∈ realificationLieSubalgebra
      ((weightedFiltration w d hwd).symbolPointwiseSubalgebra
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) v W)) (t : U → ℝ) :
    eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd) v x) ∈
      realificationLieSubalgebra (W.map (weightedAssociatedGradedEquiv w d hw hwd).toLieHom) :=
  (weightedFiltration w d hwd).realSymbolRepresentative_mem_homogeneous_image
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw) v W x hx t

theorem translationPolynomialSymbolLift_value_mem_associatedGraded_image
    (W : LieSubalgebra ℚ (weightedFiltration w d hwd).AssociatedGraded)
    (P : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      ((weightedFiltration w d hwd).symbolPointwiseSubalgebra
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) W)) (t : U → ℝ) :
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) t (translationPolynomialSymbolLift w d hw hwd P)).coord ∈
      realificationLieSubalgebra (W.map (weightedAssociatedGradedEquiv w d hw hwd).toLieHom) := by
  have h := weightedSymbolRepresentative_mem_associatedGraded_image w d hw hwd
    (fun _ : U => 1) W P.coord hP t
  change eval₂ t (translationPolynomialSymbolLift w d hw hwd P).log ∈ _
  rw [translationPolynomialSymbolLift_log]
  convert h using 1

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ)

 theorem realGradedSymbolPolynomial_filteredMap_coefficient
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (G.realGradedSymbolPolynomial c ν hG w
      (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) α =
      realificationLieHom (F.associatedGradedMap G φ hφ)
        (coefficients (F.realGradedSymbolPolynomial b ω hF w x) α) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [realificationLieHom_tmul, G.realGradedSymbolPolynomial_coefficient_tmul,
      F.realGradedSymbolPolynomial_coefficient_tmul, realificationLieHom_tmul,
      F.gradedSymbolPolynomial_filteredMap_coefficient G b ω hF c ν hG φ hφ w]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

 theorem projected_realSymbolRepresentative_coefficient
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (G.realSymbolRepresentative c ν hG w
      (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) α =
      realificationLieHom (F.homogeneousGradedProjection G c ν hG hc φ hφ)
        (coefficients (F.realGradedSymbolPolynomial b ω hF w x) α) := by
  rw [G.realSymbolRepresentative_homogeneous_coefficient c ν hG hc,
    F.realGradedSymbolPolynomial_filteredMap_coefficient G b ω hF c ν hG φ hφ w]
  change (G.homogeneousAssociatedGradedEquiv c ν hG hc).toLinearEquiv.toLinearMap.baseChange ℝ
      ((F.associatedGradedMap G φ hφ).toLinearMap.baseChange ℝ _) =
    (((G.homogeneousAssociatedGradedEquiv c ν hG hc).toLinearEquiv.toLinearMap.comp
      (F.associatedGradedMap G φ hφ).toLinearMap).baseChange ℝ) _
  rw [LinearMap.baseChange_comp]
  rfl

theorem homogeneousProjected_scalar_coordinate (η : M →ₗ[ℚ] ℚ)
    (x : F.RealPolynomialSymbol w) :
    coordinate (realifyFunctional
      (η.comp (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap)).toAddMonoidHom
        (F.realGradedSymbolPolynomial b ω hF w x) =
      coordinate (realifyFunctional η).toAddMonoidHom
        (G.realSymbolRepresentative c ν hG w
          (realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x)) := by
  apply MvPolynomial.ext
  intro α
  rw [coeff_coordinate, coeff_coordinate,
    F.projected_realSymbolRepresentative_coefficient G b ω hF c ν hG hc φ hφ w]
  exact realifyFunctional_comp η
    (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem homogeneousProjected_scalar_identity
    {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ) (η : M →ₗ[ℚ] ℚ)
    (x : F.RealPolynomialSymbol w) (y : G.RealPolynomialSymbol w)
    (P : MvPolynomial σ ℝ)
    (hmap : realificationLieHom (F.filteredPolynomialSymbolMap G φ hφ w) x = y)
    (hread : coordinate (realifyFunctional η).toAddMonoidHom
      (G.realSymbolRepresentative c ν hG w y) = P) :
    coordinate (realifyFunctional
      (η.comp (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap)).toAddMonoidHom
      (F.realGradedSymbolPolynomial b ω hF w x) = P := by
  rw [F.homogeneousProjected_scalar_coordinate G b ω hF c ν hG hc φ hφ w η x,
    hmap, hread]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold

variable {B L : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

noncomputable def detectedTranslationBaseMap :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded →ₗ[ℚ]
      (B → ℚ) :=
  (baseLinear.comp (weightedSubalgebra w d).subtype).comp
    (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
      w d hw hwd (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).toLinearMap

noncomputable def detectedTranslationBaseFunctional (i : B) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded →ₗ[ℚ] ℚ :=
  (LinearMap.proj i).comp (detectedTranslationBaseMap w d hw hwd M hM D)

 theorem detectedTranslationBaseFunctional_lie (i : B)
    (x y : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded) :
    detectedTranslationBaseFunctional w d hw hwd M hM D i ⁅x, y⁆ = 0 := by
  change (weightedTranslationGradedProjection
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
    w d hw hwd (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      ⁅x, y⁆).val.base i = 0
  rw [LieHom.map_lie]
  rfl

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold

variable {B L : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

 theorem pairResidueTranslationProjection_coordinate_logHeight {p : ℝ}
    (x : PairAlgebra (weightedSubalgebra w d) L)
    (hx : ∀ j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr x j) ≤ p)
    (i : WeightedBasisIndex w d) :
    rationalLogHeight ((weightedBasis w d hw).repr (x true) i) ≤ p := by
  have h := productProjection_coordinate_logHeight
    (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D) x hx true
    (weightedIndexOrder w d i)
  change rationalLogHeight ((weightedOrderedBasis w d hw).repr (x true)
    (weightedIndexOrder w d i)) ≤ p at h
  have he := weightedOrderedBasis_repr w d hw (x true) (weightedIndexOrder w d i)
  have he' : (weightedOrderedBasis w d hw).repr (x true) (weightedIndexOrder w d i) =
      (weightedBasis w d hw).repr (x true) i :=
    he.trans (congrArg ((weightedBasis w d hw).repr (x true)) ((weightedIndexOrder w d).symm_apply_apply i))
  exact he' ▸ h

 theorem detectedTranslationBaseFunctional_basis_apply
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i})) (i : B) (j : ι) :
    detectedTranslationBaseFunctional w d hw hwd M hM D i
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF j) =
      if ω j = w i then (b j true).val.base i else 0 := by
  let F := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
  let φ : PairAlgebra (weightedSubalgebra w d) L →ₗ⁅ℚ⁆ weightedSubalgebra w d :=
    liePiEval (R := ℚ) (M := BoolLieFamily (weightedSubalgebra w d) L) true
  exact weightedTranslationGradedProjection_basis_base F w d hw hwd φ
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    b ω hF j i

 theorem detectedTranslationBaseFunctional_basis_logHeight
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (i : B) (j : ι) :
    rationalLogHeight (detectedTranslationBaseFunctional w d hw hwd M hM D i
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF j)) ≤ p := by
  rw [detectedTranslationBaseFunctional_basis_apply w d hw hwd M hM D b ω hF i j]
  split_ifs
  · have hh := pairResidueTranslationProjection_coordinate_logHeight w d hw hwd M hM D
      (b j) (hb j) (Sum.inl i)
    exact (weightedBasis_repr_inl w d hw (b j true) i) ▸ hh
  · simpa [rationalLogHeight] using hp

 theorem detectedTranslationBaseFunctional_basis_height
    {ι : Type*} (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (i : B) (j : ι) :
    RationalHeightLE (detectedTranslationBaseFunctional w d hw hwd M hM D i
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF j))
      ⌈Real.exp p⌉₊ :=
  rationalHeightLE_ceil_exp
    (detectedTranslationBaseFunctional_basis_logHeight w d hw hwd M hM D b ω hF hp hb i j)

theorem detectedTranslationBaseFunctional_value_logHeight
    {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (x : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hx : ∀ j, rationalLogHeight
      (((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.associatedGradedBasis b ω hF).repr x j) ≤ p)
    (i : B) :
    rationalLogHeight (detectedTranslationBaseFunctional w d hw hwd M hM D i x) ≤ (p + 2)^4 :=
  rational_functional_value_logHeight _ _ hp hι
    (detectedTranslationBaseFunctional_basis_logHeight w d hw hwd M hM D b ω hF hp hb i) x hx

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial MvPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (v : σ → ℕ)

theorem realSymbolRepresentative_coordinate_top
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (i : ι) :
    coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom
      (F.realSymbolRepresentative b ω hF v (F.realSymbolOfPolynomial b ω hF v P)) =
      weightedHomogeneousComponent v (ω i)
        (coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom P) := by
  classical
  apply MvPolynomial.ext
  intro α
  rw [coeff_coordinate, coeff_weightedHomogeneousComponent, coeff_coordinate]
  simp only [LinearMap.toAddMonoidHom_coe, Basis.coord_apply]
  by_cases h : Finsupp.weight v α = ω i
  · rw [ite_eq_left h]
    have hh := (F.realSymbolRepresentative_coefficient b ω hF v _ ⟨(α, i), h⟩).trans
      (F.realSymbolOfPolynomial_coordinate b ω hF v P ⟨(α, i), h⟩)
    convert hh using 1
  · rw [ite_eq_right h]
    have hh := F.realSymbolRepresentative_coefficient_of_ne b ω hF v
      (F.realSymbolOfPolynomial b ω hF v P) α i h
    convert hh using 1

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialTranslationLie
open Module VectorPolynomial MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

variable {U B L ι : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

omit [Fintype (WeightedBasisIndex w d)] in
theorem realifyTranslationBaseFunctional_eq_coord (i : B) :
    realifyFunctional ((LinearMap.proj i).comp
      (baseLinear.comp (weightedSubalgebra w d).subtype)) =
      ((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [realifyFunctional_tmul]
    change a * (x.val.base i : ℝ) =
      ((weightedBasis w d hw).baseChange ℝ).repr (a ⊗ₜ[ℚ] x) (Sum.inl i)
    rw [Basis.baseChange_repr_tmul, weightedBasis_repr_inl]
    simp only [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hLayers : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationBaseFunctional_pairOrbitSymbol
    (p : (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1))
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) (i : B) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
      b ω hLayers (fun _ : U => 1) (detectedTranslationBaseFunctional w d hw hwd M hM D i)
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        p q b ω hLayers) =
      weightedHomogeneousComponent (fun _ : U => 1) (w i)
        (coordinate (((weightedBasis w d hw).baseChange ℝ).coord (Sum.inl i)).toAddMonoidHom p.log) := by
  let N := pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
  let G := weightedFiltration w d hwd
  let η := (LinearMap.proj i).comp (baseLinear.comp (weightedSubalgebra w d).subtype)
  have h := N.filtration.homogeneousProjected_scalar_coordinate G b ω hLayers
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw)
    (liePiEval (R := ℚ) true)
    (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
    (fun _ : U => 1) η
    (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      p q b ω hLayers).coord
  change N.filtration.scalarSymbolPolynomial b ω hLayers (fun _ : U => 1)
      (detectedTranslationBaseFunctional w d hw hwd M hM D i)
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        p q b ω hLayers) = _ at h
  have hp := pairOrbitSymbol_first_projection
    (weightedTranslationResidueNilmanifold w d hw hwd M hM) D (fun _ : U => 1)
    b ω hLayers (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) p q
  change realificationLieHom
    (N.filtration.filteredPolynomialSymbolMap G (liePiEval (R := ℚ) true)
      (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)
      (fun _ : U => 1))
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        p q b ω hLayers).coord =
    G.realSymbolOfPolynomial (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) p.log at hp
  rw [hp] at h
  dsimp only [η] at h
  rw [realifyTranslationBaseFunctional_eq_coord w d hw] at h
  exact h.trans (G.realSymbolRepresentative_coordinate_top
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1) p.log (Sum.inl i))

theorem detectedTranslationBaseFunctional_majorOrbitSymbol
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (q : D.filtration.realification.PolynomialOrbit (fun _ : U => 1)) (i : B) :
    (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
      b ω hLayers (fun _ : U => 1) (detectedTranslationBaseFunctional w d hw hwd M hM D i)
      (pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
        (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) q b ω hLayers) =
      weightedHomogeneousComponent (fun _ : U => 1) (w i) (A i) := by
  rw [detectedTranslationBaseFunctional_pairOrbitSymbol w d hw hwd M hM D b ω hLayers,
    majorTranslationPolynomialOrbit_base_coordinate w d hw hwd F hF A hA]

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open Module RationalFilteredNilmanifold VectorPolynomial

variable {B L : Type} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hF : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

 theorem detectedTranslationBase_slow_coefficients
    {σ : Type*} (u : σ → ℕ) (T : σ → ℝ) (hT : ∀ a, 0 < T a)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup u)
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hF u T (Real.exp p) E) (i : B) (α : σ →₀ ℕ) :
    |((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
        b ω hF u (detectedTranslationBaseFunctional w d hw hwd M hM D i) E).coeff α| ≤
      Real.exp ((p + 3)^3) / monomialScale T α := by
  have hcoeff := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial_slow_coefficients_of_height b ω hF u
    (detectedTranslationBaseFunctional w d hw hwd M hM D i) T hT (Real.exp_pos p).le
    (detectedTranslationBaseFunctional_basis_height w d hw hwd M hM D b ω hF hp hb i) E hE α
  exact le_trans hcoeff
    (div_le_div_of_nonneg_right
      (detectedTranslationCoordinate_slow_factor_le_exp (Fintype.card ι) hp hι)
      (monomialScale_pos T hT α).le)

 theorem detectedTranslationBase_exists_common_coefficient_grid
    {σ : Type*} (u : σ → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hB : (Fintype.card B : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup u)
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hF u m Q) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 3)^3) ∧
      ∀ i, realPolynomialCoefficientGrid q
        ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.scalarSymbolPolynomial
          b ω hF u (detectedTranslationBaseFunctional w d hw hwd M hM D i) Q) := by
  let F := (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
  obtain ⟨q, hq, hqbound, hgrid⟩ := F.scalarSymbolPolynomial_family_exists_coefficient_grid
    b ω hF u (detectedTranslationBaseFunctional w d hw hwd M hM D)
    (detectedTranslationBaseFunctional_basis_height w d hw hwd M hM D b ω hF hp hb)
    m hm Q hQ
  exact ⟨q, hq,
    detectedTranslationCoordinate_denominator_le_exp (Fintype.card B) (Fintype.card ι) m q
      hp hB hι hmp hqbound, hgrid⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
