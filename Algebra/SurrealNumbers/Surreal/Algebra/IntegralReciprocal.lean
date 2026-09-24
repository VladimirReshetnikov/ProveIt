import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral reciprocals

The general reciprocal obstruction `osq:nm:lem:reciprocal`.
An inverse of a nonzero coefficient-ring element can be integral only
when the element was already a unit. We reuse Mathlib's reflection of
units through injective integral extensions.
-/

namespace Surreal.IntegralReciprocal
noncomputable section

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F] [FaithfulSMul R F]

/-- A nonzero element has an integral reciprocal exactly when it is already a unit. -/
theorem isIntegral_inv_iff (a : R) (ha : a ≠ 0) :
    IsIntegral R (algebraMap R F a)⁻¹ ↔ IsUnit a := by
  have haF : algebraMap R F a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R F)).mpr ha
  constructor
  · intro h
    let b : integralClosure R F := ⟨(algebraMap R F a)⁻¹, h⟩
    have he : algebraMap R (integralClosure R F) a * b = 1 := by
      apply Subtype.ext
      exact mul_inv_cancel₀ haF
    letI : FaithfulSMul R (integralClosure R F) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
        intro a b hab
        apply FaithfulSMul.algebraMap_injective R F
        exact congrArg Subtype.val hab)
    exact isUnit_of_map_unit (algebraMap R (integralClosure R F)) a
      (IsUnit.of_mul_eq_one b he)
  · rintro ⟨v, rfl⟩
    have he : (algebraMap R F (v : R))⁻¹ = algebraMap R F (↑v⁻¹ : R) := by
      apply inv_eq_of_mul_eq_one_right
      simp only [← map_mul, Units.mul_inv, map_one]
    rw [he]
    exact isIntegral_algebraMap

/-- An integral reciprocal belongs to the original coefficient ring. -/
theorem inverse_mem_range (a : R) (ha : a ≠ 0)
    (h : IsIntegral R (algebraMap R F a)⁻¹) :
    (algebraMap R F a)⁻¹ ∈ (algebraMap R F).range := by
  obtain ⟨v, rfl⟩ := (isIntegral_inv_iff a ha).mp h
  refine ⟨↑v⁻¹, ?_⟩
  apply (inv_eq_of_mul_eq_one_right ?_).symm
  simp only [← map_mul, Units.mul_inv, map_one]

end
end Surreal.IntegralReciprocal
