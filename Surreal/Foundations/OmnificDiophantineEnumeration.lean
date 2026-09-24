import Surreal.Algebra.IntegerDiophantineEnumeration
import Surreal.Foundations.OmnificIntegers

/-!
# Enumeration of standard Diophantine subsets of actual omnific integers

The forward implication of `odg:def:thm:ce` on the actual universe-indexed
omnific carrier. Integer tuples, witnesses and their computability use
Mathlib's ordinary integer encodings; no enumeration of all omnific integers
or arbitrary surreal parameters is asserted.
-/

universe u
namespace Surreal.Foundations.SignSequence

/-- Any integer-coefficient finite system over actual omnific integers has an enumerable integer trace. -/
theorem omnific_diophantine_trace_re {n : ℕ} {D : Set (Fin n → OmnificInteger.{u})}
    (hD : IntegerDiophantine.Definable D) :
    REPred (fun x : Fin n → ℤ => (fun j => (x j : OmnificInteger.{u})) ∈ D) :=
  hD.integer_trace_re omnificConstantCoeff

/-- A standard-supported Diophantine set of actual omnific tuples is computably enumerable. -/
theorem omnific_standard_diophantine_re {n : ℕ} {D : Set (Fin n → ℤ)}
    (hD : IntegerDiophantine.Definable
      (IntegerDiophantine.standardImage D : Set (Fin n → OmnificInteger.{u}))) :
    REPred (· ∈ D) :=
  hD.standardImage_re omnificConstantCoeff

end Surreal.Foundations.SignSequence
