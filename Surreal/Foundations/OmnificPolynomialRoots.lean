import Surreal.Foundations.OmnificUnits
import Surreal.Surcomplex.ConstantPolynomialRoots
import Surreal.Surcomplex.NonnegativeSupportRing

/-!
# One-variable polynomial rigidity for omnific integers

The full `odg:prop:univariate`: ordinary complex and real polynomials have
only ordinary roots in the corresponding support rings, and an integer
polynomial has exactly its ordinary integer roots in the omnific ring.
The following prose consequence, transcendence of every infinite omnific
integer over the ordinary reals, uses Mathlib's `Transcendental` predicate.
-/

universe u
namespace Surreal

open Foundations

noncomputable section

namespace Surcomplex

/-- The roots in the complex support ring are exactly its constant ordinary complex roots. -/
theorem nonnegativeSupport_polynomial_root_iff (P : Polynomial ℂ) (hP : P ≠ 0)
    (z : nonnegativeSupportSubring.{u}) :
    P.eval₂ ofComplex z.val = 0 ↔
      ∃ c : ℂ, z = complexConstants c ∧ P.eval c = 0 := by
  rw [complex_polynomial_root_iff P hP]
  constructor
  · rintro ⟨c, hc, hr⟩
    exact ⟨c, Subtype.ext hc, hr⟩
  · rintro ⟨c, rfl, hr⟩
    exact ⟨c, rfl, hr⟩

end Surcomplex
namespace Foundations.SignSequence

/-- The roots in the real support ring are exactly its constant ordinary real roots. -/
theorem nonnegativeSupport_polynomial_root_iff (P : Polynomial ℝ) (hP : P ≠ 0)
    (x : nonnegativeSupportSubring.{u}) :
    P.eval₂ ofReal.toRingHom x.val = 0 ↔
      ∃ r : ℝ, x = realConstants r ∧ P.eval r = 0 := by
  rw [Surcomplex.real_polynomial_root_iff P hP]
  constructor
  · rintro ⟨r, hr, hp⟩
    exact ⟨r, Subtype.ext hr, hp⟩
  · rintro ⟨r, rfl, hp⟩
    exact ⟨r, rfl, hp⟩

/-- An omnific root of a nonzero ordinary real polynomial must be an ordinary integer. -/
theorem omnific_real_polynomial_root_iff (P : Polynomial ℝ) (hP : P ≠ 0)
    (x : OmnificInteger.{u}) :
    P.eval₂ ofReal.toRingHom (omnificToSurreal x) = 0 ↔
      ∃ n : ℤ, x = omnificIntCast n ∧ P.eval (n : ℝ) = 0 := by
  constructor
  · intro hx
    obtain ⟨r, hr, _⟩ := (Surcomplex.real_polynomial_root_iff P hP _).mp hx
    have hf : IsFinite (omnificToSurreal x) := hr ▸ finite_ofReal r
    obtain ⟨n, hn⟩ := (omnific_isFinite_iff x).mp hf
    refine ⟨n, hn, ?_⟩
    rw [hn, omnificToSurreal_intCast, ← ofReal_intCast] at hx
    change P.eval₂ ofReal.toRingHom (ofReal.toRingHom (n : ℝ)) = 0 at hx
    rw [Polynomial.eval₂_at_apply] at hx
    exact ofReal_injective (hx.trans (map_zero ofReal).symm)
  · rintro ⟨n, rfl, hn⟩
    rw [omnificToSurreal_intCast, ← ofReal_intCast]
    change P.eval₂ ofReal.toRingHom (ofReal.toRingHom (n : ℝ)) = 0
    rw [Polynomial.eval₂_at_apply, hn, map_zero]

/-- An integer polynomial acquires exactly its ordinary integer roots in the omnific ring. -/
theorem omnific_int_polynomial_root_iff (P : Polynomial ℤ) (hP : P ≠ 0)
    (x : OmnificInteger.{u}) :
    P.eval₂ omnificIntCast x = 0 ↔
      ∃ n : ℤ, x = omnificIntCast n ∧ P.eval n = 0 := by
  constructor
  · intro hx
    have hmap := congrArg omnificToSurreal hx
    rw [Polynomial.hom_eval₂, map_zero] at hmap
    have hcomp : ofReal.toRingHom.comp (Int.castRingHom ℝ) =
        omnificToSurreal.comp omnificIntCast := Subsingleton.elim _ _
    have hr : (P.map (Int.castRingHom ℝ)).eval₂ ofReal.toRingHom (omnificToSurreal x) = 0 := by
      rw [Polynomial.eval₂_map, hcomp]
      exact hmap
    obtain ⟨n, hn, _⟩ := (omnific_real_polynomial_root_iff _
      ((Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).mpr hP) x).mp hr
    refine ⟨n, hn, ?_⟩
    rw [hn, Polynomial.eval₂_at_apply] at hx
    simpa only [omnificConstantCoeff_intCast, map_zero] using congrArg omnificConstantCoeff hx
  · rintro ⟨n, rfl, hn⟩
    rw [Polynomial.eval₂_at_apply, hn, map_zero]

/-- No nonzero real polynomial vanishes at an infinite omnific integer. -/
theorem omnific_eval_ne_zero_of_not_finite (x : OmnificInteger.{u})
    (hx : ¬ IsFinite (omnificToSurreal x)) (P : Polynomial ℝ) (hP : P ≠ 0) :
    P.eval₂ ofReal.toRingHom (omnificToSurreal x) ≠ 0 := by
  intro hroot
  obtain ⟨n, hn, _⟩ := (omnific_real_polynomial_root_iff P hP x).mp hroot
  exact hx ((omnific_isFinite_iff x).mpr ⟨n, hn⟩)

/-- Every infinite actual omnific integer is transcendental over the ordinary real constants. -/
theorem omnific_transcendental_of_not_finite (x : OmnificInteger.{u})
    (hx : ¬ IsFinite (omnificToSurreal x)) :
    letI : Algebra ℝ SignSequence.{u} := ofReal.toRingHom.toAlgebra
    Transcendental ℝ (omnificToSurreal x) := by
  letI : Algebra ℝ SignSequence.{u} := ofReal.toRingHom.toAlgebra
  rintro ⟨P, hP, hroot⟩
  exact omnific_eval_ne_zero_of_not_finite x hx P hP hroot

end Foundations.SignSequence
end
end Surreal
