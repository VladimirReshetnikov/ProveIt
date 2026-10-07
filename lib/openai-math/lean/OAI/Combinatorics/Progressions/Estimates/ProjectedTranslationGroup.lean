import OAI.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction

namespace OAI

section

namespace Erdos3.PolynomialTranslationGroup

open MvPolynomial

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def baseRangeGroup (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) :
    Subgroup (PolynomialTranslationGroup σ) where
  carrier := {g | g.base ∈ A.range}
  one_mem' := A.range.zero_mem
  mul_mem' := fun ha hb => A.range.add_mem ha hb
  inv_mem' := fun ha => A.range.neg_mem ha

omit [Fintype σ] [Fintype τ] in
@[simp] theorem mem_baseRangeGroup [Fintype σ] [Fintype τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (g : PolynomialTranslationGroup σ) : g ∈ baseRangeGroup A ↔ g.base ∈ A.range := Iff.rfl

noncomputable def projectedGroupBaseCoordinates
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (g : baseRangeGroup A) : τ → ℚ :=
  (LinearEquiv.ofInjective A hA).symm ⟨g.val.base, g.property⟩

omit [Fintype σ] [Fintype τ] in
@[simp] theorem apply_projectedGroupBaseCoordinates [Fintype σ] [Fintype τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (g : baseRangeGroup A) : A (projectedGroupBaseCoordinates A hA g) = g.val.base := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective A hA).apply_symm_apply
    ⟨g.val.base, g.property⟩)

@[simp] theorem projectedGroupBaseCoordinates_one
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A) :
    projectedGroupBaseCoordinates A hA 1 = 0 := by
  apply hA
  simp

@[simp] theorem projectedGroupBaseCoordinates_mul
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (g h : baseRangeGroup A) : projectedGroupBaseCoordinates A hA (g * h) =
      projectedGroupBaseCoordinates A hA g + projectedGroupBaseCoordinates A hA h := by
  apply hA
  simp

noncomputable def projectedGroupRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A) :
    baseRangeGroup A →* PolynomialTranslationGroup τ where
  toFun g := ⟨projectedGroupBaseCoordinates A hA g,
    polynomialLinearRestriction A g.val.polynomial⟩
  map_one' := by
    apply PolynomialTranslationGroup.ext
    · exact projectedGroupBaseCoordinates_one A hA
    · exact map_zero _
  map_mul' g h := by
    apply PolynomialTranslationGroup.ext
    · exact projectedGroupBaseCoordinates_mul A hA g h
    · change polynomialLinearRestriction A
          (polynomialTranslate (-h.val.base) g.val.polynomial + h.val.polynomial) =
        polynomialTranslate (-projectedGroupBaseCoordinates A hA h)
          (polynomialLinearRestriction A g.val.polynomial) +
        polynomialLinearRestriction A h.val.polynomial
      rw [map_add]
      congr 1
      have hbase : A (-projectedGroupBaseCoordinates A hA h) = -h.val.base := by simp
      rw [← hbase, polynomialLinearRestriction_translate]

@[simp] theorem projectedGroupRestriction_base
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (g : baseRangeGroup A) :
    (projectedGroupRestriction A hA g).base = projectedGroupBaseCoordinates A hA g := rfl

@[simp] theorem projectedGroupRestriction_polynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (g : baseRangeGroup A) :
    (projectedGroupRestriction A hA g).polynomial =
      polynomialLinearRestriction A g.val.polynomial := rfl

@[simp] theorem projectedGroupRestriction_coeff_zero
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (g : baseRangeGroup A) :
    (projectedGroupRestriction A hA g).polynomial.coeff 0 = g.val.polynomial.coeff 0 :=
  coeff_zero_polynomialLinearRestriction A g.val.polynomial

theorem projectedGroupRestriction_eval
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (g : baseRangeGroup A) (x : τ → ℚ) :
    eval x (projectedGroupRestriction A hA g).polynomial = eval (A x) g.val.polynomial :=
  eval_polynomialLinearRestriction A x g.val.polynomial

omit [Fintype σ] [Fintype τ] in
@[simp] theorem exponentialElement_mem_baseRangeGroup [Fintype σ] [Fintype τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    exponentialElement (A z) P ∈ baseRangeGroup A := ⟨z, rfl⟩

noncomputable def baseRangeExponentialElement
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    baseRangeGroup A := ⟨exponentialElement (A z) P, exponentialElement_mem_baseRangeGroup A z P⟩

@[simp] theorem projectedGroupBaseCoordinates_exponentialElement
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    projectedGroupBaseCoordinates A hA (baseRangeExponentialElement A z P) = z := by
  apply hA
  rw [apply_projectedGroupBaseCoordinates]
  rfl

omit [Fintype σ] [Fintype τ] in
@[simp] theorem potentialElement_mem_baseRangeGroup [Fintype σ] [Fintype τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (V : MvPolynomial σ ℚ) (z : τ → ℚ) :
    potentialElement V (A z) ∈ baseRangeGroup A := ⟨z, rfl⟩

noncomputable def baseRangePotentialElement
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (V : MvPolynomial σ ℚ) (z : τ → ℚ) :
    baseRangeGroup A := ⟨potentialElement V (A z), potentialElement_mem_baseRangeGroup A V z⟩

@[simp] theorem projectedGroupRestriction_potentialElement
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (V : MvPolynomial σ ℚ) (z : τ → ℚ) :
    projectedGroupRestriction A hA (baseRangePotentialElement A V z) =
      potentialElement (polynomialLinearRestriction A V) z := by
  apply PolynomialTranslationGroup.ext
  · apply hA
    rw [projectedGroupRestriction_base, apply_projectedGroupBaseCoordinates]
    rfl
  · change polynomialLinearRestriction A (V - polynomialTranslate (-(A z)) V) = _
    rw [map_sub, ← map_neg A, polynomialLinearRestriction_translate]
    rfl

@[simp] theorem projectedGroupRestriction_exponentialElement
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (z : τ → ℚ) (P : MvPolynomial σ ℚ) :
    projectedGroupRestriction A hA (baseRangeExponentialElement A z P) =
      exponentialElement z (polynomialLinearRestriction A P) := by
  apply PolynomialTranslationGroup.ext
  · exact projectedGroupBaseCoordinates_exponentialElement A hA z P
  · exact polynomialLinearRestriction_exponentialCoordinate A z P

end Erdos3.PolynomialTranslationGroup

end

end OAI
