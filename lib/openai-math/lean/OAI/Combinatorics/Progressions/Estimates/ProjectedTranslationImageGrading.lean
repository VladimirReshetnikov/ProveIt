import OAI.Combinatorics.Progressions.Dynamics.ProjectedPotentialGroupIdentity

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]

theorem projectedSubalgebra_bounded
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (d : ℕ) (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hbound : U.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule) :
    (projectedSubalgebra A hA U).toSubmodule ≤ (weightedSubalgebra v d).toSubmodule := by
  rintro _ ⟨x, hx, rfl⟩
  exact projectedRestriction_mem_weightedSubalgebra A hA v w hweight d x (hbound hx)

theorem projectedSubalgebra_basisGraded
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    (d : ℕ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (hwd : ∀ i, w i ≤ d) (hvd : ∀ i, v i ≤ d)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hbound : U.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.toSubmodule.comap (weightedSubalgebra w d).subtype)) :
    BasisGradedSubmodule (weightedBasis v d hv) (weightedBasisGrade v d)
      ((projectedSubalgebra A hA U).toSubmodule.comap (weightedSubalgebra v d).subtype) := by
  intro j x hx
  change x.val ∈ projectedSubalgebra A hA U at hx
  obtain ⟨y, hy, he⟩ := hx
  let z : weightedSubalgebra w d := ⟨y.val, hbound hy⟩
  have hz : z.val ∈ baseRange A := y.property
  let zp := basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j z
  have hzp : zp.val ∈ U := hgraded j z hy
  have hzpr := weightedBasis_projection_mem_baseRange A v w hweight d j hw z hz
  change (basisGradeProjection (weightedBasis v d hv) (weightedBasisGrade v d) j x).val ∈
    projectedSubalgebra A hA U
  refine ⟨⟨zp.val, hzpr⟩, hzp, ?_⟩
  have hcomm := projectedRestriction_basisGradeProjection A hA v w hweight d j hw hv hwd hvd z hz
  have hx' : (⟨projectedRestriction A hA ⟨z.val, hz⟩,
      projectedRestriction_mem_weightedSubalgebra A hA v w hweight d ⟨z.val, hz⟩ z.property⟩ :
      weightedSubalgebra v d) = x := Subtype.ext he
  rw [hx'] at hcomm
  exact hcomm

theorem exists_potential_on_projected_base_of_graded
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (v : τ → ℕ) (w : σ → ℕ)
    (hweight : ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0)
    {d : ℕ} (hd : 0 < d) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (hwd : ∀ i, w i ≤ d) (hvd : ∀ i, v i ≤ d)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hbound : U.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.toSubmodule.comap (weightedSubalgebra w d).subtype))
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (hbase : ∀ z : τ → ℚ, ∃ x ∈ U, x.base = A z) :
    ∃ V : MvPolynomial τ ℚ, V.IsWeightedHomogeneous v d ∧
      ∀ x : baseRange A, x.val ∈ U →
        scalarDirectionalDerivative (projectedBaseCoordinates A hA x) V =
          polynomialLinearRestriction A x.val.polynomial := by
  apply exists_potential_on_projected_base A hA w v hd hv hvd U
    (fun _ hx => topProjection_mem_of_basisGraded w d hw hd U.toSubmodule hbound hgraded hx)
    frequency hfrequency hkill hbase
  · exact projectedSubalgebra_bounded A hA v w hweight d U hbound
  · exact projectedSubalgebra_basisGraded A hA v w hweight d hw hv hwd hvd U hbound hgraded

end Erdos3.PolynomialTranslationLie

end

end OAI
