import Surreal.HahnSeries.TailoredDiophantineConstants
import Surreal.Algebra.RecursiveSaturation
import Surreal.HahnSeries.Characteristic

/-!
# The explicit omitted type for number-field coefficients

The number-field clause of `odg:def:thm:saturation`, given an admissible
prime pair with nonsquare radicands. The guard is constructed explicitly,
rather than assumed to define the coefficient ring. Existence of such a
pair for every number field is proved in `NumberFieldTailoredGuard`; the
unconditional specialization is in `NumberFieldArithmeticConstants`.
-/

namespace Surreal.HahnSeries
open AlgebraicOmittedType RecursiveSaturation
noncomputable section

variable {Γ K L : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field K] [NumberField K] [Field L] [CharZero L]

local instance tailoredSaturationIntermediateStructure (A : Subring (nonpositiveSupportSubring Γ L)) :
    FirstOrder.Ring.CompatibleRing A := FirstOrder.Ring.compatibleRingOfRing A

/-- Every finite subset of the explicit native type is realized, but the full type is omitted. -/
theorem numberField_tailored_type_finitelySatisfiable_and_omitted {p q : ℕ}
    (h : TailoredIntersectivePolynomial.Admissible p q)
    (hp : ¬IsSquare (p : K)) (hq : ¬IsSquare (q : K)) (hpq : ¬IsSquare ((p * q : ℕ) : K))
    (o : Subring K) (j : K →+* L) (A : Subring (nonpositiveSupportSubring Γ L))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (j.comp o.subtype).range) :
    FinitelySatisfiable A (formulas (TailoredArithmeticGuard.guard p q)) ∧
      ¬ ∃ x : A, Realizes (formulas (TailoredArithmeticGuard.guard p q)) x :=
  numberField_finitelySatisfiable_and_omitted o.subtype Subtype.val_injective
    (intermediateConstants (j.comp o.subtype) A hA) (TailoredArithmeticGuard.guard p q)
    (numberField_intermediate_tailored_guard_iff h hp hq hpq o j A hA)

/-- The explicitly constructed guard witnesses failure of recursive saturation. -/
theorem numberField_tailored_not_recursivelySaturated {p q : ℕ}
    (h : TailoredIntersectivePolynomial.Admissible p q)
    (hp : ¬IsSquare (p : K)) (hq : ¬IsSquare (q : K)) (hpq : ¬IsSquare ((p * q : ℕ) : K))
    (o : Subring K) (j : K →+* L) (A : Subring (nonpositiveSupportSubring Γ L))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (j.comp o.subtype).range) :
    ¬ RecursivelySaturated A :=
  numberField_not_recursivelySaturated o.subtype Subtype.val_injective
    (intermediateConstants (j.comp o.subtype) A hA) (TailoredArithmeticGuard.guard p q)
    (numberField_intermediate_tailored_guard_iff h hp hq hpq o j A hA)

end
end Surreal.HahnSeries
