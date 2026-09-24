import Surreal.Algebra.NormalizationFiniteTargets
import Surreal.Surcomplex.GaussianNormalizationEmbedding

/-!
# No finite quotients of the actual omnific normalizations

The actual real and Gaussian clauses of `osq:nm:thm:nofinite`.
Both native integral closures receive the ordinary real algebraic
integers, which alone exclude unital maps to nonzero finite rings.
The target may be noncommutative and live in any universe.
-/

universe u v
noncomputable section
namespace Surreal.Foundations.SignSequence

/-- The real algebraic integers as constants in the actual omnific normalization. -/
def realAlgebraicIntegersToOmnificNormalization :
    integralClosure ℤ ℝ →+* integralClosure OmnificInteger SignSequence.{u} :=
  NormalizationFiniteTargets.realAlgebraicIntegersToNormalization ofReal.toRingHom

@[simp] theorem realAlgebraicIntegersToOmnificNormalization_value (x : integralClosure ℤ ℝ) :
    (realAlgebraicIntegersToOmnificNormalization x : SignSequence.{u}) = ofReal x := rfl

/-- The actual omnific normalization has no unital homomorphism to a nonzero finite ring. -/
theorem omnific_normalization_no_finite_ring_hom {R : Type v}
    [Ring R] [Finite R] [Nontrivial R]
    (f : integralClosure OmnificInteger SignSequence.{u} →+* R) : False :=
  NormalizationFiniteTargets.no_finite_ring_hom_of_realAlgebraicIntegers
    realAlgebraicIntegersToOmnificNormalization f

/-- The only ideal giving a finite quotient of the real normalization is the whole ring. -/
theorem omnific_normalization_finite_quotient_eq_top
    (J : Ideal (integralClosure OmnificInteger SignSequence.{u}))
    [Finite ((integralClosure OmnificInteger SignSequence.{u}) ⧸ J)] : J = ⊤ :=
  NormalizationFiniteTargets.finite_quotient_eq_top realAlgebraicIntegersToOmnificNormalization J

/-- Every proper quotient of the actual real normalization is infinite. -/
theorem omnific_normalization_infinite_quotient
    (J : Ideal (integralClosure OmnificInteger SignSequence.{u})) (hJ : J ≠ ⊤) :
    Infinite ((integralClosure OmnificInteger SignSequence.{u}) ⧸ J) :=
  NormalizationFiniteTargets.infinite_quotient_of_ne_top
    realAlgebraicIntegersToOmnificNormalization J hJ

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex
open Foundations

/-- The real algebraic integers as constants in the actual Gaussian normalization. -/
def realAlgebraicIntegersToGaussianNormalization :
    integralClosure ℤ ℝ →+* integralClosure GaussianOmnificInteger Surcomplex.{u} :=
  realNormalizationToGaussian.comp SignSequence.realAlgebraicIntegersToOmnificNormalization

@[simp] theorem realAlgebraicIntegersToGaussianNormalization_value (x : integralClosure ℤ ℝ) :
    (realAlgebraicIntegersToGaussianNormalization x : Surcomplex.{u}) =
      ofReal (SignSequence.ofReal x) := rfl

/-- Gaussian normalization also excludes finite nonzero rings, including noncommutative targets. -/
theorem gaussianOmnific_normalization_no_finite_ring_hom {R : Type v}
    [Ring R] [Finite R] [Nontrivial R]
    (f : integralClosure GaussianOmnificInteger Surcomplex.{u} →+* R) : False :=
  NormalizationFiniteTargets.no_finite_ring_hom_of_realAlgebraicIntegers
    realAlgebraicIntegersToGaussianNormalization f

/-- The only ideal giving a finite quotient of Gaussian normalization is the whole ring. -/
theorem gaussianOmnific_normalization_finite_quotient_eq_top
    (J : Ideal (integralClosure GaussianOmnificInteger Surcomplex.{u}))
    [Finite ((integralClosure GaussianOmnificInteger Surcomplex.{u}) ⧸ J)] : J = ⊤ :=
  NormalizationFiniteTargets.finite_quotient_eq_top realAlgebraicIntegersToGaussianNormalization J

/-- Every proper quotient of the actual Gaussian normalization is infinite. -/
theorem gaussianOmnific_normalization_infinite_quotient
    (J : Ideal (integralClosure GaussianOmnificInteger Surcomplex.{u})) (hJ : J ≠ ⊤) :
    Infinite ((integralClosure GaussianOmnificInteger Surcomplex.{u}) ⧸ J) :=
  NormalizationFiniteTargets.infinite_quotient_of_ne_top
    realAlgebraicIntegersToGaussianNormalization J hJ

end Surreal.Surcomplex
end
