import Surreal.Algebra.NaturalDiophantineIntegers
import Surreal.Foundations.OmnificDiophantineStandardImages

/-!
# Mathlib natural Diophantine sets in the actual omnific ring

Arithmetic prerequisites for `odg:def:thm:ce`. Mathlib's natural arithmetic
Diophantine theorems, including exponentiation, are realized by finite native
integer-polynomial systems on standard tuples in the actual omnific carrier.
This asserts ordinary natural powers, not a definition of surreal exponentiation.
-/

universe u
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Every Mathlib natural Diophantine set lifts exactly to its standard omnific image. -/
theorem omnific_natural_diophantine {n : ℕ} {D : Set (Fin n → ℕ)} (hD : Dioph D) :
    IntegerDiophantine.Definable
      (IntegerDiophantine.standardImage (IntegerDiophantine.naturalImage D) :
        Set (Fin n → OmnificInteger.{u})) :=
  (omnific_standardImage_definable_iff _).mpr
    (IntegerDiophantine.naturalImage_definable_of_dioph hD)

/-- The ordinary natural power graph is Diophantine on the actual standard omnific tuples. -/
theorem omnific_natural_power_diophantine :
    IntegerDiophantine.Definable
      (IntegerDiophantine.standardImage (IntegerDiophantine.naturalImage
        {x : Fin 3 → ℕ | x 0 ^ x 1 = x 2}) : Set (Fin 3 → OmnificInteger.{u})) :=
  (omnific_standardImage_definable_iff _).mpr
    IntegerDiophantine.natural_power_integer_graph_definable

end
end Surreal.Foundations.SignSequence
