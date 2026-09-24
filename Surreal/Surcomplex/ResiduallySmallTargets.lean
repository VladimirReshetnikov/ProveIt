import Surreal.Algebra.ResiduallySmallRings
import Surreal.Surcomplex.GaussianSmallTargets

/-!
# Omnific maps into residually small targets

The actual real and Gaussian instances of `osq:thm:residual`, including
rings of finite polynomials over small coefficients with arbitrarily large
variable types. No small family of detecting maps is assumed.
-/

universe u v w
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Residual smallness of the target suffices to kill the whole real infinite ideal. -/
theorem omnific_residuallySmall_hom_purelyInfinite {B : Type v} [Ring B]
    (hB : ResiduallySmall.{u, v, w} B) (φ : OmnificInteger.{u} →+* B)
    (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) : φ x = 0 := by
  apply hB.eq_of_observations
  intro S _ _ π
  rw [map_zero]
  exact omnific_small_hom_purelyInfinite (π.comp φ).toNonUnitalRingHom x hx

/-- The universal real constant quotient also represents maps into residually small rings. -/
theorem omnific_residuallySmall_hom_factors {B : Type v} [Ring B]
    (hB : ResiduallySmall.{u, v, w} B) (φ : OmnificInteger.{u} →+* B) :
    ∃! ψ : ℤ →+* B, ψ.comp omnificConstantCoeff = φ :=
  ResiduallySmall.factors_through_retraction omnificConstantCoeff omnificIntCast
    omnificConstantCoeff_intCast (fun _ _ _ f x => omnific_small_hom_eq_constant f.toNonUnitalRingHom x)
    hB φ

/-- Such a real map still has exactly the integer constant-term formula. -/
theorem omnific_residuallySmall_ringHom_eq_constant {B : Type v} [Ring B]
    (hB : ResiduallySmall.{u, v, w} B) (φ : OmnificInteger.{u} →+* B) (x : OmnificInteger.{u}) :
    φ x = (omnificConstantCoeff x : B) := by
  obtain ⟨ψ, hψ, _⟩ := omnific_residuallySmall_hom_factors hB φ
  have he : ψ = Int.castRingHom B := Subsingleton.elim _ _
  rw [he] at hψ
  exact (RingHom.congr_fun hψ x).symm

/-- Even arbitrarily many polynomial variables do not permit a new map on the full omnific ring. -/
theorem omnific_mvPolynomial_ringHom_eq_constant (E : Type v) [CommRing E] [Small.{u} E]
    (σ : Type w) (φ : OmnificInteger.{u} →+* MvPolynomial σ E) (x : OmnificInteger.{u}) :
    φ x = (omnificConstantCoeff x : MvPolynomial σ E) :=
  omnific_residuallySmall_ringHom_eq_constant (ResiduallySmall.mvPolynomial E σ) φ x

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- Residually small targets cannot detect a Gaussian purely infinite element. -/
theorem gaussianOmnific_residuallySmall_hom_purelyInfinite {B : Type v} [Ring B]
    (hB : ResiduallySmall.{u, v, w} B) (φ : GaussianOmnificInteger.{u} →+* B)
    (x : GaussianOmnificInteger.{u}) (hx : x ∈ gaussianOmnificPurelyInfiniteIdeal.{u}) : φ x = 0 := by
  apply hB.eq_of_observations
  intro S _ _ π
  rw [map_zero]
  exact gaussianOmnific_small_hom_purelyInfinite (π.comp φ).toNonUnitalRingHom x hx

/-- Gaussian constant extraction also represents every map to a residually small ring. -/
theorem gaussianOmnific_residuallySmall_hom_factors {B : Type v} [Ring B]
    (hB : ResiduallySmall.{u, v, w} B) (φ : GaussianOmnificInteger.{u} →+* B) :
    ∃! ψ : GaussianInt →+* B, ψ.comp gaussianOmnificConstantCoeff.{u} = φ :=
  ResiduallySmall.factors_through_retraction gaussianOmnificConstantCoeff.{u}
    gaussianOmnificConstants.{u} gaussianOmnificConstantCoeff_constants
    (fun _ _ _ f x => gaussianOmnific_small_hom_eq_constant f.toNonUnitalRingHom x) hB φ

/-- The Gaussian factorization remains valid for polynomials in any type of variables. -/
theorem gaussianOmnific_mvPolynomial_hom_factors (E : Type v) [CommRing E] [Small.{u} E]
    (σ : Type w) (φ : GaussianOmnificInteger.{u} →+* MvPolynomial σ E) :
    ∃! ψ : GaussianInt →+* MvPolynomial σ E, ψ.comp gaussianOmnificConstantCoeff.{u} = φ :=
  gaussianOmnific_residuallySmall_hom_factors (ResiduallySmall.mvPolynomial E σ) φ

end
end Surreal.Surcomplex
