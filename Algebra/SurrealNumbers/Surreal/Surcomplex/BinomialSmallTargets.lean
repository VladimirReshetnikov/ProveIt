import Surreal.Foundations.OmnificSmallTargets
import Surreal.Surcomplex.GaussianBinomialRoots

/-!
# Binomial root nonexistence is invisible in every small ring image

The remaining small-target clauses of `osq:nm:thm:invisible` and
`osq:nm:rem:rootinN`, for both actual omnific rings. Restriction to the real
omnific ring kills every positive real monomial even for Gaussian sources.
The target may be noncommutative. Its smallness is relative to the birthday
universe, not a finiteness assumption.
-/

universe u v w
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Every unital small-target map kills each positive omnific monomial. -/
theorem omnific_small_ringHom_monomial {S : Type v} [Ring S] [Small.{u} S]
    (φ : OmnificInteger.{u} →+* S) (g : SignSequence.{u}) (hg : 0 < g) :
    φ (omnificMonomial g hg) = 0 :=
  omnific_small_hom_purelyInfinite φ.toNonUnitalRingHom _ (omnificMonomial_mem_purelyInfinite g hg)

/-- The absent omnific root has the explicit solution one in every small ring image. -/
theorem omnific_binomial_small_image_root {S : Type v} [Ring S] [Small.{u} S]
    (φ : OmnificInteger.{u} →+* S) (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) :
    (1 : S) ^ m = φ (omnificMonomial g hg) + 1 := by
  rw [omnific_small_ringHom_monomial, _root_.zero_add, one_pow]

/-- In any extension ring, the image of an adjoined binomial root has power one. -/
theorem omnific_small_extension_root_pow {B : Type w} [Ring B]
    (ι : OmnificInteger.{u} →+* B) {S : Type v} [Ring S] [Small.{u} S]
    (ψ : B →+* S) (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) (r : B)
    (hr : r ^ m = ι (omnificMonomial g hg) + 1) : ψ r ^ m = 1 := by
  have hz := omnific_small_ringHom_monomial (ψ.comp ι) g hg
  change ψ (ι (omnificMonomial g hg)) = 0 at hz
  rw [← map_pow, hr, map_add, map_one, hz, _root_.zero_add]

/-- The specified positive root, as an element of the native integral closure. -/
def omnificNormalizationBinomialRoot (g : SignSequence.{u}) (hg : 0 < g)
    (m : ℕ) (hm : m ≠ 0) : integralClosure OmnificInteger SignSequence.{u} :=
  ⟨omnificBinomialRoot g hg m, omnificBinomialRoot_isIntegral g hg m hm⟩

/-- Every small image of the normalization sends the specified root to an mth root of one. -/
theorem omnific_normalization_binomial_small_image {S : Type v} [Ring S] [Small.{u} S]
    (ψ : integralClosure OmnificInteger SignSequence.{u} →+* S)
    (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) (hm : m ≠ 0) :
    ψ (omnificNormalizationBinomialRoot g hg m hm) ^ m = 1 := by
  apply omnific_small_extension_root_pow
    (algebraMap OmnificInteger (integralClosure OmnificInteger SignSequence.{u})) ψ g hg
  apply Subtype.ext
  exact omnificBinomialRoot_pow g hg m hm

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- Restriction to real omnific integers kills every positive real monomial in Gaussian sources. -/
theorem gaussianOmnific_small_ringHom_real_monomial {S : Type v} [Ring S] [Small.{u} S]
    (φ : GaussianOmnificInteger.{u} →+* S) (g : SignSequence.{u}) (hg : 0 < g) :
    φ (omnificToGaussian (SignSequence.omnificMonomial g hg)) = 0 :=
  SignSequence.omnific_small_ringHom_monomial (φ.comp omnificToGaussian) g hg

/-- Every small ring image of the Gaussian omnific ring also solves the image equation at one. -/
theorem gaussianOmnific_binomial_small_image_root {S : Type v} [Ring S] [Small.{u} S]
    (φ : GaussianOmnificInteger.{u} →+* S) (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ) :
    (1 : S) ^ m = φ (omnificToGaussian (SignSequence.omnificMonomial g hg)) + 1 := by
  rw [gaussianOmnific_small_ringHom_real_monomial, zero_add, one_pow]

/-- Each actual Gaussian normalization root has power one in every small ring image. -/
theorem gaussianOmnific_normalization_binomial_small_image {S : Type v} [Ring S] [Small.{u} S]
    (ψ : integralClosure GaussianOmnificInteger.{u} Surcomplex.{u} →+* S)
    (g : SignSequence.{u}) (hg : 0 < g) (m : ℕ)
    (r : integralClosure GaussianOmnificInteger.{u} Surcomplex.{u})
    (hr : (r : Surcomplex.{u}) ^ m = ofReal (SignSequence.omegaPower g) + 1) : ψ r ^ m = 1 := by
  apply SignSequence.omnific_small_extension_root_pow
    ((algebraMap GaussianOmnificInteger.{u} (integralClosure GaussianOmnificInteger.{u} Surcomplex.{u})).comp
      omnificToGaussian) ψ g hg
  apply Subtype.ext
  exact hr

end
end Surreal.Surcomplex
