import Surreal.Foundations.OmnificNormalizationDensity
import Surreal.Algebra.NormalizationConductor
import Surreal.Surcomplex.GaussianIntegralSlices
import Surreal.Surcomplex.OmnificDecomposableFibers
import Surreal.Surcomplex.Modulus

/-!
# Real normalization inside the Gaussian normalization

The embeddings and modulus gap needed by `osq:nm:lem:intpart` and
`osq:nm:thm:complexnormal`. Coordinates of Gaussian omnific integers are
actual real omnific integers, and real integral elements remain integral
under the canonical inclusion in the surcomplex field.
-/

universe u
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- The canonical inclusion of actual real omnific integers into Gaussian omnific integers. -/
def omnificToGaussian : SignSequence.OmnificInteger.{u} →+* GaussianOmnificInteger.{u} :=
  omnificSupportInclusion.codRestrict gaussianOmnificSubring (fun x => by
    refine ⟨(SignSequence.omnificConstantCoeff x : GaussianInt), ?_⟩
    simp only [map_intCast, constantCoeff_omnificSupportInclusion])

@[simp] theorem gaussianOmnificToSurcomplex_of_omnific (x : SignSequence.OmnificInteger.{u}) :
    gaussianOmnificToSurcomplex (omnificToGaussian x) = ofReal (SignSequence.omnificToSurreal x) := rfl

/-- The real coordinate stays in the actual omnific ring. -/
def gaussianOmnificRe (z : GaussianOmnificInteger.{u}) : SignSequence.OmnificInteger.{u} :=
  ⟨nonnegativeRe z.val, ((mem_gaussianOmnificSubring_iff z.val).mp z.property).1⟩

/-- The imaginary coordinate stays in the actual omnific ring. -/
def gaussianOmnificIm (z : GaussianOmnificInteger.{u}) : SignSequence.OmnificInteger.{u} :=
  ⟨nonnegativeIm z.val, ((mem_gaussianOmnificSubring_iff z.val).mp z.property).2⟩

@[simp] theorem gaussianOmnificRe_value (z : GaussianOmnificInteger.{u}) :
    SignSequence.omnificToSurreal (gaussianOmnificRe z) = (gaussianOmnificToSurcomplex z).re := rfl

@[simp] theorem gaussianOmnificIm_value (z : GaussianOmnificInteger.{u}) :
    SignSequence.omnificToSurreal (gaussianOmnificIm z) = (gaussianOmnificToSurcomplex z).im := rfl

/-- Every nonzero Gaussian omnific integer has actual surreal modulus at least one. -/
theorem one_le_gaussianOmnific_modulus (z : GaussianOmnificInteger.{u}) (hz : z ≠ 0) :
    1 ≤ modulus (gaussianOmnificToSurcomplex z) := by
  by_cases hr : (gaussianOmnificToSurcomplex z).re = 0
  · have hi : (gaussianOmnificToSurcomplex z).im ≠ 0 := by
      intro hi
      apply hz
      apply gaussianOmnificToSurcomplex_injective
      rw [map_zero]
      exact Surcomplex.ext hr hi
    exact (NormalizationConductor.one_le_abs SignSequence.existsUnique_omnific_integerPart
      (gaussianOmnificIm z) hi).trans (abs_im_le_modulus _)
  · exact (NormalizationConductor.one_le_abs SignSequence.existsUnique_omnific_integerPart
      (gaussianOmnificRe z) hr).trans (abs_re_le_modulus _)

/-- Real integral elements map into the actual Gaussian normalization. -/
theorem gaussianOmnific_isIntegral_ofReal {x : SignSequence.{u}}
    (hx : IsIntegral SignSequence.OmnificInteger x) :
    IsIntegral GaussianOmnificInteger (ofReal x) :=
  hx.map_of_comp_eq omnificToGaussian ofReal (by
    apply RingHom.ext
    intro a
    exact gaussianOmnificToSurcomplex_of_omnific a)

/-- The imaginary unit is integral over the Gaussian omnific ring. -/
theorem gaussianOmnific_I_isIntegral : IsIntegral GaussianOmnificInteger.{u} (I : Surcomplex.{u}) := by
  simpa only [ofComplex_I] using
    (gaussianOmnific_ofComplex_isIntegral_iff.{u} Complex.I).mpr Complex.isIntegral_int_I

/-- The real normalization embeds as a subring of the Gaussian normalization. -/
def realNormalizationToGaussian :
    integralClosure SignSequence.OmnificInteger SignSequence.{u} →+*
      integralClosure GaussianOmnificInteger Surcomplex.{u} :=
  (ofReal.comp (integralClosure SignSequence.OmnificInteger SignSequence.{u}).val.toRingHom).codRestrict
    (integralClosure GaussianOmnificInteger Surcomplex.{u}).toSubring
    (fun x => gaussianOmnific_isIntegral_ofReal x.property)

@[simp] theorem realNormalizationToGaussian_value
    (x : integralClosure SignSequence.OmnificInteger SignSequence.{u}) :
    (realNormalizationToGaussian x : Surcomplex) = ofReal (x : SignSequence) := rfl

end
end Surreal.Surcomplex
