import OAI.Combinatorics.Progressions.Linear.RealCoordinateImageSpan

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def baseLinear : PolynomialTranslationLie σ →ₗ[ℚ] (σ → ℚ) where
  toFun x := x.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def baseRange (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) :
    LieSubalgebra ℚ (PolynomialTranslationLie σ) :=
  { A.range.comap baseLinear with
    lie_mem' := by
      intro x y _ _
      change (0 : σ → ℚ) ∈ A.range
      exact Submodule.zero_mem _ }

omit [Fintype τ] in
@[simp] theorem mem_baseRange (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (x : PolynomialTranslationLie σ) : x ∈ baseRange A ↔ x.base ∈ A.range := Iff.rfl

noncomputable def baseRangeBase (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) :
    baseRange A →ₗ[ℚ] A.range where
  toFun x := ⟨x.val.base, x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def projectedBaseCoordinates (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) : baseRange A →ₗ[ℚ] (τ → ℚ) :=
  (LinearEquiv.ofInjective A hA).symm.toLinearMap.comp (baseRangeBase A)

omit [Fintype τ] in
@[simp] theorem apply_projectedBaseCoordinates (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (x : baseRange A) :
    A (projectedBaseCoordinates A hA x) = x.val.base := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective A hA).apply_symm_apply
    ⟨x.val.base, x.property⟩)

noncomputable def projectedRestriction (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) : baseRange A →ₗ⁅ℚ⁆ PolynomialTranslationLie τ where
  toFun x := ⟨projectedBaseCoordinates A hA x, polynomialLinearRestriction A x.val.polynomial⟩
  map_add' x y := by
    apply PolynomialTranslationLie.ext
    · exact map_add _ _ _
    · exact map_add _ _ _
  map_smul' r x := by
    apply PolynomialTranslationLie.ext
    · exact map_smul _ _ _
    · exact map_smul _ _ _
  map_lie' := by
    intro x y
    apply PolynomialTranslationLie.ext
    · apply hA
      rw [apply_projectedBaseCoordinates]
      change (0 : σ → ℚ) = A 0
      exact (map_zero A).symm
    · change polynomialLinearRestriction A (scalarDirectionalDerivative x.val.base y.val.polynomial -
        scalarDirectionalDerivative y.val.base x.val.polynomial) =
        scalarDirectionalDerivative (projectedBaseCoordinates A hA x)
          (polynomialLinearRestriction A y.val.polynomial) -
        scalarDirectionalDerivative (projectedBaseCoordinates A hA y)
          (polynomialLinearRestriction A x.val.polynomial)
      rw [map_sub, scalarDirectionalDerivative_linearRestriction,
        scalarDirectionalDerivative_linearRestriction,
        apply_projectedBaseCoordinates, apply_projectedBaseCoordinates]

@[simp] theorem projectedRestriction_base (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (x : baseRange A) :
    (projectedRestriction A hA x).base = projectedBaseCoordinates A hA x := rfl

@[simp] theorem projectedRestriction_polynomial (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (x : baseRange A) :
    (projectedRestriction A hA x).polynomial = polynomialLinearRestriction A x.val.polynomial := rfl

theorem projectedRestriction_base_surjective
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (U : LieSubalgebra ℚ (baseRange A))
    (hbase : ∀ z : τ → ℚ, ∃ x ∈ U, x.val.base = A z) :
    ∀ z : τ → ℚ, ∃ x ∈ U.map (projectedRestriction A hA), x.base = z := by
  intro z
  obtain ⟨x,hx,hxz⟩ := hbase z
  refine ⟨projectedRestriction A hA x, ⟨x,hx,rfl⟩, ?_⟩
  apply hA
  rw [projectedRestriction_base, apply_projectedBaseCoordinates, hxz]

theorem projectedRestriction_eq_zero_iff
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A) (x : baseRange A) :
    projectedRestriction A hA x = 0 ↔
      x.val.base = 0 ∧ polynomialLinearRestriction A x.val.polynomial = 0 := by
  constructor
  · intro hx
    have hb : projectedBaseCoordinates A hA x = 0 := congrArg PolynomialTranslationLie.base hx
    refine ⟨?_, congrArg PolynomialTranslationLie.polynomial hx⟩
    rw [← apply_projectedBaseCoordinates A hA x, hb, map_zero]
  · rintro ⟨hb,hp⟩
    apply PolynomialTranslationLie.ext
    · apply hA
      rw [projectedRestriction_base, apply_projectedBaseCoordinates, hb, base_zero, map_zero]
    · exact hp

theorem eval_projectedRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (x : baseRange A) (z : τ → ℚ) :
    eval z (projectedRestriction A hA x).polynomial = eval (A z) x.val.polynomial :=
  eval_polynomialLinearRestriction A z x.val.polynomial

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]

theorem projectedRestriction_mem_weightedLayer
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (d j : ℕ) (x : baseRange A) (hx : x.val ∈ weightedLayer w d j) :
    projectedRestriction A hA x ∈ weightedLayer v d j := by
  constructor
  · apply linearMap_reflects_weighted_base_layer A v w hweight hA j
    rw [projectedRestriction_base, apply_projectedBaseCoordinates]
    exact hx.1
  · exact polynomialLinearRestriction_mem_weightedSupportDrop A v w hweight hx.2

theorem projectedRestriction_mem_weightedSubalgebra
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (d : ℕ) (x : baseRange A) (hx : x.val ∈ weightedSubalgebra w d) :
    projectedRestriction A hA x ∈ weightedSubalgebra v d :=
  projectedRestriction_mem_weightedLayer A hA v w hweight d 1 x hx

theorem weightedBasis_projection_mem_baseRange
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (d j : ℕ) (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d)
    (hx : x.val ∈ baseRange A) :
    (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val ∈
      baseRange A := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun k => if v k = j then z k else 0, ?_⟩
  rw [linearMap_coordinateGradeProjection A v w hweight, hz]
  funext i
  exact (weightedBasis_projection_base w d j hw x i).symm

theorem projectedBaseCoordinates_basisGradeProjection
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (d j : ℕ) (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d)
    (hx : x.val ∈ baseRange A) :
    projectedBaseCoordinates A hA
      ⟨(basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val,
        weightedBasis_projection_mem_baseRange A v w hweight d j hw x hx⟩ =
      fun k => if v k = j then projectedBaseCoordinates A hA ⟨x.val, hx⟩ k else 0 := by
  apply hA
  rw [apply_projectedBaseCoordinates, linearMap_coordinateGradeProjection A v w hweight,
    apply_projectedBaseCoordinates]
  funext i
  exact weightedBasis_projection_base w d j hw x i

theorem projectedRestriction_basisGradeProjection
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (d j : ℕ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (hwd : ∀ i, w i ≤ d) (hvd : ∀ i, v i ≤ d)
    (x : weightedSubalgebra w d) (hx : x.val ∈ baseRange A) :
    projectedRestriction A hA
      ⟨(basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val,
        weightedBasis_projection_mem_baseRange A v w hweight d j hw x hx⟩ =
      (basisGradeProjection (weightedBasis v d hv) (weightedBasisGrade v d) j
        ⟨projectedRestriction A hA ⟨x.val, hx⟩,
          projectedRestriction_mem_weightedSubalgebra A hA v w hweight d
            ⟨x.val, hx⟩ x.property⟩).val := by
  apply PolynomialTranslationLie.ext
  · rw [projectedRestriction_base,
      projectedBaseCoordinates_basisGradeProjection A hA v w hweight d j hw x hx]
    funext i
    symm
    exact weightedBasis_projection_base v d j hv _ i
  · rw [projectedRestriction_polynomial]
    dsimp only
    by_cases hj : j ≤ d
    · rw [weightedBasis_projection_polynomial_eq_component w d j hw hj,
        weightedBasis_projection_polynomial_eq_component v d j hv hj,
        polynomialLinearRestriction_weightedHomogeneousComponent A v w hweight]
      rfl
    · rw [weightedBasis_projection_eq_zero_of_lt w d j hw hwd (by omega),
        weightedBasis_projection_eq_zero_of_lt v d j hv hvd (by omega)]
      exact map_zero _

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open Module
open scoped TensorProduct

variable {B : Type*} [Fintype B]

theorem weightedTranslationBase_projection
    (w : B → ℕ) (d j : ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedSubalgebra w d) :
    (baseLinear.comp (weightedSubalgebra w d).subtype)
        (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x) =
      basisGradeProjection (Pi.basisFun ℚ B) w j x.val.base := by
  funext i
  have h := basisGradeProjection_repr (Pi.basisFun ℚ B) w j x.val.base i
  simp only [Pi.basisFun_repr] at h
  change (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x).val.base i = _
  rw [weightedBasis_projection_base]
  exact h.symm

theorem weightedTranslationBase_image_graded
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (weightedSubalgebra w d))
    (hU : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U) :
    BasisGradedSubmodule (Pi.basisFun ℚ B) w
      (U.map (baseLinear.comp (weightedSubalgebra w d).subtype)) := by
  intro j y hy
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x,
    hU j x hx, ?_⟩
  exact weightedTranslationBase_projection w d j hw x

theorem weightedTranslationBase_mask_mem
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (weightedSubalgebra w d))
    (hU : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U)
    (j : ℕ) (x : B → ℚ)
    (hx : x ∈ U.map (baseLinear.comp (weightedSubalgebra w d).subtype)) :
    (fun i => if w i = j then x i else 0) ∈
      U.map (baseLinear.comp (weightedSubalgebra w d).subtype) := by
  have h := weightedTranslationBase_image_graded w d hw U hU j x hx
  have he : basisGradeProjection (Pi.basisFun ℚ B) w j x =
      (fun i => if w i = j then x i else 0) := by
    funext i
    simpa only [Pi.basisFun_repr] using
      basisGradeProjection_repr (Pi.basisFun ℚ B) w j x i
  rwa [he] at h

theorem weightedTranslationBase_real_image_graded
    {J : Type*} (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (weightedSubalgebra w d))
    (hU : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U)
    (g : J → weightedSubalgebra w d) (hg : Submodule.span ℚ (Set.range g) = U) :
    BasisGradedSubmodule (Pi.basisFun ℝ B) w
      ((U.baseChange ℝ).map
        (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))) := by
  let ℓ := baseLinear.comp (weightedSubalgebra w d).subtype
  rw [realifyCoordinateMap_image_eq_span U g hg ℓ]
  intro j z hz
  let K := Submodule.span ℝ (Set.range (fun a i => ((g a).val.base i : ℝ)))
  change basisGradeProjection (Pi.basisFun ℝ B) w j z ∈ K
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    have hga : g a ∈ U := by rw [← hg]; exact Submodule.subset_span ⟨a, rfl⟩
    have hproj := hU j (g a) hga
    have ht := Submodule.tmul_mem_baseChange_of_mem (1 : ℝ) hproj
    have hm := realifyCoordinateMap_mem_span U g hg ℓ ht
    change _ ∈ K at hm
    convert hm using 1
    funext i
    have hp := basisGradeProjection_repr (Pi.basisFun ℝ B) w j
      (fun i => ((g a).val.base i : ℝ)) i
    simp only [Pi.basisFun_repr] at hp
    change (basisGradeProjection (Pi.basisFun ℝ B) w j
      (fun i => ((g a).val.base i : ℝ))) i = _
    rw [hp, realifyCoordinateMap_tmul, one_mul]
    change (if w i = j then ((g a).val.base i : ℝ) else 0) =
      ((basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j (g a)).val.base i : ℝ)
    rw [weightedBasis_projection_base]
    split_ifs <;> simp
  | zero => simpa only [map_zero] using K.zero_mem
  | add x y hx hy hxp hyp =>
    rw [map_add]
    exact K.add_mem hxp hyp
  | smul c x hx hxp =>
    rw [map_smul]
    exact K.smul_mem c hxp

end Erdos3.PolynomialTranslationLie

end

end OAI
