import Surreal.Algebra.GaussianEndomorphisms
import Surreal.Surcomplex.GaussianSmallTargets

/-!
# Constant-term rigidity of Gaussian omnific endomorphisms

The Gaussian clause of `osq:cor:rigid`, strengthened from automorphisms
to all unital endomorphisms for the induced identity-or-conjugation action.
The purely infinite ideal is preserved and reflected by endomorphisms and
carried onto itself by automorphisms.
-/

universe u
namespace Surreal.Surcomplex

/-- Every Gaussian omnific endomorphism acts on constants by identity or conjugation. -/
theorem gaussianOmnific_endomorphism_constant
    (σ : GaussianOmnificInteger.{u} →+* GaussianOmnificInteger.{u}) :
    gaussianOmnificConstantCoeff.comp σ = gaussianOmnificConstantCoeff ∨
      gaussianOmnificConstantCoeff.comp σ =
        (starRingEnd GaussianInt).comp gaussianOmnificConstantCoeff := by
  let φ := gaussianOmnificConstantCoeff.comp σ
  have h := (gaussianOmnificSmallRingHomEquiv.{u} GaussianInt).symm_apply_apply φ
  rcases OrdinaryRingMaps.gaussian_endomorphism_eq_id_or_star
    (gaussianOmnificSmallRingHomEquiv.{u} GaussianInt φ) with hi | hi
  · rw [hi] at h
    exact Or.inl h.symm
  · rw [hi] at h
    exact Or.inr h.symm

/-- Constant-zero elements are preserved and reflected by every Gaussian endomorphism. -/
theorem gaussianOmnific_endomorphism_purelyInfinite_iff
    (σ : GaussianOmnificInteger.{u} →+* GaussianOmnificInteger.{u})
    (x : GaussianOmnificInteger.{u}) :
    σ x ∈ gaussianOmnificPurelyInfiniteIdeal ↔ x ∈ gaussianOmnificPurelyInfiniteIdeal := by
  change gaussianOmnificConstantCoeff (σ x) = 0 ↔ gaussianOmnificConstantCoeff x = 0
  rcases gaussianOmnific_endomorphism_constant σ with h | h
  · have he := RingHom.congr_fun h x
    change gaussianOmnificConstantCoeff (σ x) = gaussianOmnificConstantCoeff x at he
    rw [he]
  · have he := RingHom.congr_fun h x
    change gaussianOmnificConstantCoeff (σ x) = star (gaussianOmnificConstantCoeff x) at he
    rw [he, star_eq_zero]

/-- The inverse image of the Gaussian purely infinite ideal is itself. -/
theorem gaussianOmnific_endomorphism_comap_purelyInfinite
    (σ : GaussianOmnificInteger.{u} →+* GaussianOmnificInteger.{u}) :
    gaussianOmnificPurelyInfiniteIdeal.{u}.comap σ = gaussianOmnificPurelyInfiniteIdeal := by
  ext x
  exact gaussianOmnific_endomorphism_purelyInfinite_iff σ x

/-- Every Gaussian omnific automorphism carries the purely infinite ideal onto itself. -/
theorem gaussianOmnific_automorphism_map_purelyInfinite
    (σ : GaussianOmnificInteger.{u} ≃+* GaussianOmnificInteger.{u}) :
    gaussianOmnificPurelyInfiniteIdeal.{u}.map σ.toRingHom = gaussianOmnificPurelyInfiniteIdeal := by
  conv_lhs => rw [← gaussianOmnific_endomorphism_comap_purelyInfinite σ.toRingHom]
  exact Ideal.map_comap_of_surjective _ σ.surjective _

end Surreal.Surcomplex
