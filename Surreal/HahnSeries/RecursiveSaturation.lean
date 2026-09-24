import Surreal.Algebra.RecursiveSaturation
import Surreal.HahnSeries.AlgebraicOmittedType

/-!
# Failure of recursive saturation in intermediate Hahn rings

The recursive-saturation conclusion of `odg:def:thm:saturation`, with the
integer and Gaussian guards instantiated. No nontriviality of the exponent
group or constant-term retraction is required.
-/

namespace Surreal.HahnSeries
open RecursiveSaturation

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field K] [CharZero K] [CommRing O]

noncomputable local instance (A : Subring (nonpositiveSupportSubring Γ K)) :
    FirstOrder.Ring.CompatibleRing A := FirstOrder.Ring.compatibleRingOfRing A

/-- Definable algebraic coefficient rings prevent recursive saturation. -/
theorem intermediate_not_recursivelySaturated (i : O →+* K) (hi : Function.Injective i)
    (hroot : ∀ a : O, IntersectivePolynomial.value a ≠ 0)
    (hordinary : ∀ a : O, DiophantineConstants.Xi a) (hAlg : ∀ a : O, IsAlgebraic ℤ a)
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ i.range) :
    ¬ RecursivelySaturated A :=
  not_recursivelySaturated_of_algebraicType ArithmeticGuards.integerGuard
    (intermediate_algebraicType_finitelySatisfiable A)
    (intermediate_algebraicType_omitted i hi hroot hordinary hAlg A hA)

/-- Every integer-constant intermediate Hahn ring fails recursive saturation. -/
theorem integer_intermediate_not_recursivelySaturated
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range) :
    ¬ RecursivelySaturated A :=
  not_recursivelySaturated_of_algebraicType ArithmeticGuards.integerGuard
    (intermediate_algebraicType_finitelySatisfiable A)
    (integer_intermediate_algebraicType_omitted A hA)

/-- Every Gaussian-constant intermediate Hahn ring fails recursive saturation. -/
theorem gaussian_intermediate_not_recursivelySaturated (i : GaussianInt →+* K)
    (hi : Function.Injective i) (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ i.range) :
    ¬ RecursivelySaturated A :=
  not_recursivelySaturated_of_algebraicType ArithmeticGuards.integerGuard
    (intermediate_algebraicType_finitelySatisfiable A)
    (gaussian_intermediate_algebraicType_omitted i hi A hA)

end Surreal.HahnSeries
