import Surreal.Surcomplex.DecomposableKernelCriterion
import Surreal.Foundations.OmnificPurelyInfiniteIdeal

/-!
# The real and complex infinite ideals are not small

The universe-relative proper-class prerequisite for the paragraph following
`odg:dec:cor:converse`. A small real infinite ideal would generate itself
from a small set, contradicting the established common-monomial divisor
argument. Its inclusion in the complex ideal transfers the obstruction.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- The real purely infinite omnific ideal is not small in the lower universe. -/
theorem omnificPurelyInfinite_not_small : ¬ Small.{u} SignSequence.omnificPurelyInfiniteIdeal.{u} := by
  intro h
  letI := h
  exact SignSequence.omnificPurelyInfiniteIdeal_ne_span_small
    (SignSequence.omnificPurelyInfiniteIdeal : Set SignSequence.OmnificInteger) (Ideal.span_eq _)

/-- Include the real infinite ideal in the actual complex infinite ideal. -/
def realPurelyInfiniteToComplex (t : SignSequence.omnificPurelyInfiniteIdeal.{u}) :
    complexPurelyInfiniteSubmodule.{u} :=
  ⟨omnificSupportInclusion t.val, by
    change constantCoeff (omnificSupportInclusion t.val) = 0
    rw [constantCoeff_omnificSupportInclusion]
    have h : SignSequence.omnificConstantCoeff t.val = 0 := t.property
    rw [h, Int.cast_zero]⟩

/-- Inclusion of infinite real terms into complex terms is injective. -/
theorem realPurelyInfiniteToComplex_injective :
    Function.Injective (realPurelyInfiniteToComplex.{u}) := by
  intro x y h
  apply Subtype.val_injective
  apply SignSequence.omnificToSurreal_injective
  apply ofReal_injective
  exact congrArg (fun z : complexPurelyInfiniteSubmodule => z.val.val) h

/-- The complex infinite ideal is also not small in the lower universe. -/
theorem complexPurelyInfinite_not_small : ¬ Small.{u} complexPurelyInfiniteSubmodule.{u} := by
  intro h
  letI := h
  exact omnificPurelyInfinite_not_small (small_of_injective realPurelyInfiniteToComplex_injective)

end
end Surreal.Surcomplex
