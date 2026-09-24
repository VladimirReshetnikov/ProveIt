import Surreal.Algebra.NumberFieldTailoredGuard
import Surreal.HahnSeries.TailoredRecursiveSaturation

/-!
# Native number-field coefficient definitions and omitted types

The constant-definition clause of `odg:def:thm:numberfield` and the remaining
number-field clause of `odg:def:thm:saturation`. The verified tailored primes
are supplied internally for every number field, with no guard-correctness or
prime-existence hypothesis. The remaining detector, ideal and graph clauses
are proved in `NumberFieldDetector` and `NumberFieldDetectorFormulas`.
-/

namespace Surreal.HahnSeries
open AlgebraicOmittedType RecursiveSaturation
noncomputable section

variable {Γ K L : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field K] [NumberField K] [Field L] [CharZero L]

local instance numberFieldGuardIntermediateStructure (A : Subring (nonpositiveSupportSubring Γ L)) :
    FirstOrder.Ring.CompatibleRing A := FirstOrder.Ring.compatibleRingOfRing A

/-- For every number field and every coefficient subring, the chosen guard defines its image. -/
theorem numberField_guard_iff (o : Subring K) (j : K →+* L)
    (A : Subring (nonpositiveSupportSubring Γ L))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (j.comp o.subtype).range) (x : A) :
    (NumberFieldTailoredGuard.guard K).Realize (fun _ => x) ↔
      x ∈ (intermediateConstants (j.comp o.subtype) A hA).range :=
  numberField_intermediate_tailored_guard_iff (NumberFieldTailoredGuard.pair K).admissible
    (NumberFieldTailoredGuard.pair K).p_nonsquare (NumberFieldTailoredGuard.pair K).q_nonsquare
    (NumberFieldTailoredGuard.pair K).pq_nonsquare o j A hA x

/-- Every such coefficient image has a native parameter-free ring-language definition. -/
theorem numberField_constants_definable (o : Subring K) (j : K →+* L)
    (A : Subring (nonpositiveSupportSubring Γ L))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (j.comp o.subtype).range) :
    (∅ : Set A).Definable₁ FirstOrder.Language.ring
      (intermediateConstants (j.comp o.subtype) A hA).range :=
  numberField_intermediate_constants_definable (NumberFieldTailoredGuard.pair K).admissible
    (NumberFieldTailoredGuard.pair K).p_nonsquare (NumberFieldTailoredGuard.pair K).q_nonsquare
    (NumberFieldTailoredGuard.pair K).pq_nonsquare o j A hA

/-- Every number-field coefficient ring gives the explicit finitely satisfiable omitted type. -/
theorem numberField_type_finitelySatisfiable_and_omitted (o : Subring K) (j : K →+* L)
    (A : Subring (nonpositiveSupportSubring Γ L))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (j.comp o.subtype).range) :
    FinitelySatisfiable A (formulas (NumberFieldTailoredGuard.guard K)) ∧
      ¬ ∃ x : A, Realizes (formulas (NumberFieldTailoredGuard.guard K)) x :=
  numberField_finitelySatisfiable_and_omitted o.subtype Subtype.val_injective
    (intermediateConstants (j.comp o.subtype) A hA) (NumberFieldTailoredGuard.guard K)
    (numberField_guard_iff o j A hA)

/-- Every intermediate Hahn ring with number-field coefficients fails recursive saturation. -/
theorem numberField_intermediate_not_recursivelySaturated (o : Subring K) (j : K →+* L)
    (A : Subring (nonpositiveSupportSubring Γ L))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (j.comp o.subtype).range) :
    ¬ RecursivelySaturated A :=
  numberField_not_recursivelySaturated o.subtype Subtype.val_injective
    (intermediateConstants (j.comp o.subtype) A hA) (NumberFieldTailoredGuard.guard K)
    (numberField_guard_iff o j A hA)

end
end Surreal.HahnSeries
