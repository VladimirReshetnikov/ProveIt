import Surreal.Algebra.OrdinaryRingMaps

/-!
# Endomorphisms of the ordinary Gaussian integers

The constant-ring rigidity used in `osq:cor:rigid`: every unital
endomorphism is identity or conjugation. Mathlib's quadratic-generator
extensionality reduces the classification to the two roots of minus one.
-/

namespace Surreal.OrdinaryRingMaps

/-- Every endomorphism of the ordinary Gaussian integers is identity or conjugation. -/
theorem gaussian_endomorphism_eq_id_or_star (φ : GaussianInt →+* GaussianInt) :
    φ = RingHom.id GaussianInt ∨ φ = starRingEnd GaussianInt := by
  have hi : (Zsqrtd.sqrtd : GaussianInt) ^ 2 = -1 := by
    rw [pow_two, Zsqrtd.dmuld, Int.cast_neg, Int.cast_one]
  have h := (gaussianRingHomEquiv GaussianInt φ).property
  change φ Zsqrtd.sqrtd ^ 2 = -1 at h
  rw [← hi, sq_eq_sq_iff_eq_or_eq_neg] at h
  rcases h with h | h
  · exact Or.inl (Zsqrtd.hom_ext _ _ h)
  · apply Or.inr
    apply Zsqrtd.hom_ext
    rw [h]
    rfl

end Surreal.OrdinaryRingMaps

