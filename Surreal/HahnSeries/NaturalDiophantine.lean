import Surreal.Algebra.NaturalDiophantineIntegers
import Surreal.HahnSeries.DiophantineStandardImages

/-!
# Lifting Mathlib's natural Diophantine sets into Hahn rings

Arithmetic prerequisites for `odg:def:thm:ce`: every existing Mathlib `Dioph`
result yields a finite integer-polynomial system defining exactly the
standard natural image in the full integer-coefficient pullback.
-/

namespace Surreal.HahnSeries
noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CharZero K] {n : ℕ}
local notation "A" => coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)

/-- Natural Diophantine sets have exact standard-supported finite-system definitions. -/
theorem integerRestricted_natural_diophantine {D : Set (Fin n → ℕ)} (hD : Dioph D) :
    IntegerDiophantine.Definable
      (IntegerDiophantine.standardImage (IntegerDiophantine.naturalImage D) : Set (Fin n → A)) :=
  (integerRestricted_standardImage_definable_iff _).mpr
    (IntegerDiophantine.naturalImage_definable_of_dioph hD)

/-- Ordinary natural exponentiation has a Diophantine graph with every free coordinate standard. -/
theorem integerRestricted_natural_power_diophantine :
    IntegerDiophantine.Definable
      (IntegerDiophantine.standardImage (IntegerDiophantine.naturalImage
        {x : Fin 3 → ℕ | x 0 ^ x 1 = x 2}) : Set (Fin 3 → A)) :=
  (integerRestricted_standardImage_definable_iff _).mpr
    IntegerDiophantine.natural_power_integer_graph_definable

end
end Surreal.HahnSeries
