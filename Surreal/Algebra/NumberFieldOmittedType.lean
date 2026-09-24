import Surreal.Algebra.AlgebraicOmittedType
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.Integral

/-!
# Omitted types for definable number-field coefficient rings

The denominator-clearing step of `odg:def:thm:saturation`, using Mathlib's
fraction-field algebraicity theorem. This applies to arbitrary subrings of
number fields, without assuming integrality or finite generation. The native
guard is an input with its defining property; constructing the tailored
number-field guard of `odg:def:thm:numberfield` is a separate obligation.
-/

namespace Surreal.AlgebraicOmittedType
open FirstOrder FirstOrder.Language

/-- An element of any ring embedded in a number field has a nonzero integer annihilator. -/
theorem numberField_subring_isAlgebraic {K O : Type*} [Field K] [NumberField K]
    [CommRing O] (j : O →+* K) (hj : Function.Injective j) (a : O) :
    IsAlgebraic ℤ a := by
  apply (isAlgebraic_algHom_iff j.toIntAlgHom hj).mp
  exact (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (IsAlgebraic.of_finite ℚ (j a))

/-- Any native guard defining a number-field coefficient image yields the source's omitted type. -/
theorem numberField_finitelySatisfiable_and_omitted
    {R K O : Type*} [CommRing R] [CharZero R] [FirstOrder.Ring.CompatibleRing R]
    [Field K] [NumberField K] [CommRing O]
    (j : O →+* K) (hj : Function.Injective j) (i : O →+* R)
    (δ : Language.ring.Formula (Fin 1))
    (hδ : ∀ x : R, δ.Realize (fun _ => x) ↔ x ∈ i.range) :
    FinitelySatisfiable R (formulas δ) ∧ ¬ ∃ x : R, Realizes (formulas δ) x :=
  finitelySatisfiable_and_omitted_of_range δ i hδ (numberField_subring_isAlgebraic j hj)

end Surreal.AlgebraicOmittedType
