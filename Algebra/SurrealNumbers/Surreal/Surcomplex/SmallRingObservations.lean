import Surreal.Surcomplex.GaussianSmallTargets
import Mathlib.Algebra.Ring.ULift

/-!
# What all small ring observations identify

The actual real and Gaussian instances of `osq:cor:observations`.
Two elements have the same image in every small ring exactly when their
ordinary constant terms agree. The purely infinite ideals are the literal
intersections of all these kernels, even with target universe fixed arbitrarily.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- All small unital ring observations identify precisely the equal-constant pairs. -/
theorem omnific_small_observations_iff (x y : OmnificInteger.{u}) :
    omnificConstantCoeff x = omnificConstantCoeff y ↔
      ∀ (S : Type v) [Ring S] [Small.{u} S] (φ : OmnificInteger.{u} →+* S), φ x = φ y := by
  constructor
  · intro h S _ _ φ
    rw [omnific_small_ringHom_eq_constant φ x, omnific_small_ringHom_eq_constant φ y, h]
  · intro h
    have he := h (ULift.{v} ℤ) (ULift.ringEquiv.symm.toRingHom.comp omnificConstantCoeff)
    exact ULift.up_injective he

/-- The purely infinite ideal is the common kernel of all small unital ring observations. -/
theorem omnificPurelyInfiniteIdeal_eq_iInf_small_kernels :
    omnificPurelyInfiniteIdeal.{u} =
      ⨅ (S : Type v) (_ : Ring S) (_ : Small.{u} S) (φ : OmnificInteger.{u} →+* S), RingHom.ker φ := by
  ext x
  simp only [Ideal.mem_iInf, RingHom.mem_ker]
  change omnificConstantCoeff x = 0 ↔ _
  have h := omnific_small_observations_iff.{u, v} x 0
  simpa only [map_zero] using h

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- All small Gaussian omnific ring observations identify exactly the equal-constant pairs. -/
theorem gaussianOmnific_small_observations_iff (x y : GaussianOmnificInteger.{u}) :
    gaussianOmnificConstantCoeff.{u} x = gaussianOmnificConstantCoeff.{u} y ↔
      ∀ (S : Type v) [Ring S] [Small.{u} S] (φ : GaussianOmnificInteger.{u} →+* S), φ x = φ y := by
  constructor
  · intro h S _ _ φ
    have hx := gaussianOmnific_small_hom_eq_constant φ.toNonUnitalRingHom x
    have hy := gaussianOmnific_small_hom_eq_constant φ.toNonUnitalRingHom y
    exact hx.trans ((congrArg (fun d => φ (gaussianOmnificConstants.{u} d)) h).trans hy.symm)
  · intro h
    have he := h (ULift.{v} GaussianInt)
      (ULift.ringEquiv.symm.toRingHom.comp gaussianOmnificConstantCoeff.{u})
    exact ULift.up_injective he

/-- The Gaussian infinite ideal is the literal common kernel of every small unital observation. -/
theorem gaussianOmnificPurelyInfiniteIdeal_eq_iInf_small_kernels :
    gaussianOmnificPurelyInfiniteIdeal.{u} =
      ⨅ (S : Type v) (_ : Ring S) (_ : Small.{u} S)
        (φ : GaussianOmnificInteger.{u} →+* S), RingHom.ker φ := by
  ext x
  simp only [Ideal.mem_iInf, RingHom.mem_ker]
  have h := gaussianOmnific_small_observations_iff.{u, v} x 0
  simpa only [map_zero] using h

end
end Surreal.Surcomplex
