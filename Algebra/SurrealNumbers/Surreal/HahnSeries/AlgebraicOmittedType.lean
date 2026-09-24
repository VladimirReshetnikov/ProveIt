import Surreal.Algebra.AlgebraicOmittedType
import Surreal.HahnSeries.DiophantineConstants
import Surreal.HahnSeries.Characteristic

/-!
# The explicit algebraic type in intermediate Hahn rings

The finite-satisfiability and omission clauses of `odg:def:thm:saturation`.
Only the exact intersection with the coefficient field is needed; no
constant-term retraction or nontriviality of the exponent group is assumed.
-/

namespace Surreal.HahnSeries
open FirstOrder FirstOrder.Language AlgebraicOmittedType
noncomputable section

variable {Γ K O : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field K] [CharZero K] [CommRing O]

local instance omittedTypeIntermediateStructure (A : Subring (nonpositiveSupportSubring Γ K)) :
    FirstOrder.Ring.CompatibleRing A := FirstOrder.Ring.compatibleRingOfRing A

/-- Every intermediate Hahn ring realizes every finite subset of the explicit type. -/
theorem intermediate_algebraicType_finitelySatisfiable
    (A : Subring (nonpositiveSupportSubring Γ K)) :
    FinitelySatisfiable A (formulas ArithmeticGuards.integerGuard) :=
  xi_finitelySatisfiable

/-- If Xi defines algebraic coefficients, the intermediate ring omits the explicit type. -/
theorem intermediate_algebraicType_omitted (i : O →+* K) (hi : Function.Injective i)
    (hroot : ∀ a : O, IntersectivePolynomial.value a ≠ 0)
    (hordinary : ∀ a : O, DiophantineConstants.Xi a)
    (hAlg : ∀ a : O, IsAlgebraic ℤ a)
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ i.range) :
    ¬ ∃ x : A, Realizes (formulas ArithmeticGuards.integerGuard) x := by
  apply xi_omitted_of_range (intermediateConstants i A hA) _ hAlg
  intro x hx
  obtain ⟨a, ha⟩ := (intermediate_xi_iff i hi hroot hordinary A hA x).mp hx
  exact ⟨a, Subtype.ext ha.symm⟩

/-- The integer-constant intermediate rings omit the same parameter-free type. -/
theorem integer_intermediate_algebraicType_omitted
    (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range) :
    ¬ ∃ x : A, Realizes (formulas ArithmeticGuards.integerGuard) x :=
  intermediate_algebraicType_omitted (Int.castRingHom K) Int.cast_injective
    IntersectivePolynomial.integer_value_ne_zero DiophantineConstants.integer_xi
    (fun a => isAlgebraic_algebraMap a) A hA

/-- The Gaussian-constant intermediate rings omit the same type, using quadratic annihilators. -/
theorem gaussian_intermediate_algebraicType_omitted (i : GaussianInt →+* K)
    (hi : Function.Injective i) (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ i.range) :
    ¬ ∃ x : A, Realizes (formulas ArithmeticGuards.integerGuard) x :=
  intermediate_algebraicType_omitted i hi IntersectivePolynomial.gaussian_value_ne_zero
    DiophantineConstants.gaussian_xi (zsqrtd_isAlgebraic (-1)) A hA

end
end Surreal.HahnSeries
