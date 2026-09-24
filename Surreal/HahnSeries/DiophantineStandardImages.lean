import Surreal.Algebra.IntegerDiophantineGuards
import Surreal.HahnSeries.DiophantineEnumeration

/-!
# Exact Diophantine transfer for standard-supported Hahn sets

The guarded lifting step of `odg:def:thm:ce`, including its order-free
characteristic-zero generalization. The existing three-equation integer
guard works without order or square roots in the coefficient field.
-/

namespace Surreal.HahnSeries
noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CharZero K] {n : ℕ}
local notation "A" => coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)

/-- The finite polynomial guard defines exactly the native integer casts. -/
theorem integerRestricted_diophantine_guard_iff (x : A) :
    IntegerDiophantine.integerGuard.Holds (fun _ => x) ↔ ∃ z : ℤ, x = (z : A) := by
  rw [IntegerDiophantine.holds_integerGuard_iff, integer_intermediate_xi_iff
    (coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K))
    (coefficientRestricted_constants_intersection (Int.castRingHom K))]
  apply exists_congr
  intro a
  rw [map_intCast]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- Integer Diophantine sets lift exactly to their standard-supported images over every characteristic-zero field. -/
theorem integerRestricted_standardImage_definable_iff (D : Set (Fin n → ℤ)) :
    IntegerDiophantine.Definable (IntegerDiophantine.standardImage D : Set (Fin n → A)) ↔
      IntegerDiophantine.Definable D :=
  IntegerDiophantine.standardImage_definable_iff
    (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom K) Int.cast_injective)
    IntegerDiophantine.integerGuard integerRestricted_diophantine_guard_iff D

end
end Surreal.HahnSeries
