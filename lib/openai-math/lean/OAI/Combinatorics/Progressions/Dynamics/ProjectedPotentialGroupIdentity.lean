import OAI.Combinatorics.Progressions.Estimates.ProjectedTranslationGroup
import OAI.Combinatorics.Progressions.Estimates.WeightedTranslationBaseGrading

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def projectedSubalgebra (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (U : LieSubalgebra ℚ (PolynomialTranslationLie σ)) :
    LieSubalgebra ℚ (PolynomialTranslationLie τ) :=
  (U.comap (baseRange A).incl).map (projectedRestriction A hA)

theorem projected_pure_constant_zero
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (w : σ → ℕ) (d : ℕ) (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (P : MvPolynomial τ ℚ)
    (hP : (⟨0,P⟩ : PolynomialTranslationLie τ) ∈ projectedSubalgebra A hA U) :
    P.coeff 0 = 0 := by
  obtain ⟨x,hx,hxP⟩ := hP
  have hb : x.val.base = 0 := by
    rw [← apply_projectedBaseCoordinates A hA x]
    have hz : projectedBaseCoordinates A hA x = 0 := congrArg PolynomialTranslationLie.base hxP
    rw [hz, map_zero]
  have hpure : (⟨0,x.val.polynomial⟩ : PolynomialTranslationLie σ) ∈ U := by
    have he : (⟨0,x.val.polynomial⟩ : PolynomialTranslationLie σ) = x.val :=
      PolynomialTranslationLie.ext hb.symm rfl
    rw [he]
    exact hx
  have hz := pure_constant_zero_of_top_frequency w d U hgraded frequency hfrequency hkill
    x.val.polynomial hpure
  have hp : polynomialLinearRestriction A x.val.polynomial = P :=
    congrArg PolynomialTranslationLie.polynomial hxP
  rw [← hp, coeff_zero_polynomialLinearRestriction, hz]

noncomputable def projectedPotentialRelation
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (w : σ → ℕ) (d : ℕ) (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) :
    Erdos3.PolynomialPotentialRelation τ where
  space := relationSpace (projectedSubalgebra A hA U)
  bracket_mem := by
    intro x P z Q hx hz
    exact (mem_relationSpace _ _ _).mpr (raw_lie_mem _ x z P Q
      ((mem_relationSpace _ _ _).mp hx) ((mem_relationSpace _ _ _).mp hz))
  pure_constant_zero := fun P hP => projected_pure_constant_zero A hA w d U hgraded
    frequency hfrequency hkill P ((mem_relationSpace _ _ _).mp hP)

theorem projectedSubalgebra_base_surjective
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hbase : ∀ z : τ → ℚ, ∃ x ∈ U, x.base = A z) :
    Function.Surjective (fun x : projectedSubalgebra A hA U => x.val.base) := by
  intro z
  obtain ⟨x,hx,hxz⟩ := hbase z
  have hr : x ∈ baseRange A := ⟨z,hxz.symm⟩
  let y : baseRange A := ⟨x,hr⟩
  refine ⟨⟨projectedRestriction A hA y, ⟨y,hx,rfl⟩⟩, ?_⟩
  apply hA
  change A (projectedBaseCoordinates A hA y) = A z
  rw [apply_projectedBaseCoordinates]
  exact hxz

theorem exists_potential_on_projected_base
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (w : σ → ℕ) (v : τ → ℕ) {d : ℕ} (hd : 0 < d)
    (hv : ∀ i, 0 < v i) (hvd : ∀ i, v i ≤ d)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (hbase : ∀ z : τ → ℚ, ∃ x ∈ U, x.base = A z)
    (hbound : (projectedSubalgebra A hA U).toSubmodule ≤
      (weightedSubalgebra v d).toSubmodule)
    (hprojectedgraded : BasisGradedSubmodule (weightedBasis v d hv) (weightedBasisGrade v d)
      ((projectedSubalgebra A hA U).toSubmodule.comap (weightedSubalgebra v d).subtype)) :
    ∃ V : MvPolynomial τ ℚ, V.IsWeightedHomogeneous v d ∧
      ∀ x : baseRange A, x.val ∈ U →
        scalarDirectionalDerivative (projectedBaseCoordinates A hA x) V =
          polynomialLinearRestriction A x.val.polynomial := by
  classical
  obtain ⟨P,hlift,hhom⟩ := exists_ambient_homogeneous_coordinate_lifts v d hv
    (projectedSubalgebra A hA U).toSubmodule hbound hprojectedgraded
    (projectedSubalgebra_base_surjective A hA U hbase)
  let rel := projectedPotentialRelation A hA w d U hgraded frequency hfrequency hkill
  have hrel : ∀ i, (Pi.single i 1,P i) ∈ rel.space := hlift
  obtain ⟨V,hV,h⟩ := rel.exists_weighted_potential P hrel v hd hvd hhom
  refine ⟨V,hV,fun x hx => ?_⟩
  exact h _ _ (show projectedRestriction A hA x ∈ projectedSubalgebra A hA U from ⟨x,hx,rfl⟩)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def projectedFastGenerators (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (U : LieSubalgebra ℚ (PolynomialTranslationLie σ)) :
    Set (PolynomialTranslationGroup.baseRangeGroup A) :=
  {g | ∃ x : baseRange A, x.val ∈ U ∧ g =
    PolynomialTranslationGroup.baseRangeExponentialElement A
      (projectedBaseCoordinates A hA x) x.val.polynomial}

theorem projectedFastGenerators_mem_potential
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ)) (V : MvPolynomial τ ℚ)
    (hV : ∀ x : baseRange A, x.val ∈ U →
      scalarDirectionalDerivative (projectedBaseCoordinates A hA x) V =
        polynomialLinearRestriction A x.val.polynomial)
    {g : PolynomialTranslationGroup.baseRangeGroup A}
    (hg : g ∈ projectedFastGenerators A hA U) :
    PolynomialTranslationGroup.projectedGroupRestriction A hA g ∈
      PolynomialTranslationGroup.potentialSubgroup V := by
  obtain ⟨x,hx,rfl⟩ := hg
  rw [PolynomialTranslationGroup.projectedGroupRestriction_exponentialElement, ← hV x hx,
    PolynomialTranslationGroup.exponentialElement_potential]
  exact (PolynomialTranslationGroup.mem_potentialSubgroup V _).mpr rfl

theorem projectedFastSubgroup_potential_identity
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ)) (V : MvPolynomial τ ℚ)
    (hV : ∀ x : baseRange A, x.val ∈ U →
      scalarDirectionalDerivative (projectedBaseCoordinates A hA x) V =
        polynomialLinearRestriction A x.val.polynomial)
    {g : PolynomialTranslationGroup.baseRangeGroup A}
    (hg : g ∈ Subgroup.closure (projectedFastGenerators A hA U)) :
    polynomialLinearRestriction A g.val.polynomial =
      V - polynomialTranslate
        (-(PolynomialTranslationGroup.projectedGroupRestriction A hA g).base) V := by
  have hle : Subgroup.closure (projectedFastGenerators A hA U) ≤
      (PolynomialTranslationGroup.potentialSubgroup V).comap
        (PolynomialTranslationGroup.projectedGroupRestriction A hA) := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    exact projectedFastGenerators_mem_potential A hA U V hV hx
  exact (PolynomialTranslationGroup.mem_potentialSubgroup V _).mp (hle hg)

omit [Fintype τ] in
private theorem eval_polynomialTranslate (x h : τ → ℚ) (P : MvPolynomial τ ℚ) :
    eval x (polynomialTranslate h P) = eval (x + h) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [hp, Pi.add_apply]

theorem projectedFastSubgroup_eval_potential_identity
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ)) (V : MvPolynomial τ ℚ)
    (hV : ∀ x : baseRange A, x.val ∈ U →
      scalarDirectionalDerivative (projectedBaseCoordinates A hA x) V =
        polynomialLinearRestriction A x.val.polynomial)
    (W : MvPolynomial σ ℚ) (hW : polynomialLinearRestriction A W = V)
    {g : PolynomialTranslationGroup.baseRangeGroup A}
    (hg : g ∈ Subgroup.closure (projectedFastGenerators A hA U)) (z : τ → ℚ) :
    eval (A z) g.val.polynomial = eval (A z) W - eval (A z - g.val.base) W := by
  have h := congrArg (eval z) (projectedFastSubgroup_potential_identity A hA U V hV hg)
  rw [eval_polynomialLinearRestriction, map_sub, eval_polynomialTranslate, ← hW,
    eval_polynomialLinearRestriction, eval_polynomialLinearRestriction] at h
  simpa only [map_add, map_neg, sub_eq_add_neg,
    PolynomialTranslationGroup.projectedGroupRestriction_base,
    PolynomialTranslationGroup.apply_projectedGroupBaseCoordinates] using h

end Erdos3.PolynomialTranslationLie

end

end OAI
