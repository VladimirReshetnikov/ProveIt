import Surreal.Algebra.IntegerDiophantineEnumeration
import Surreal.HahnSeries.ConstantTermGraph

/-!
# Computably enumerable integer traces in Hahn coefficient pullbacks

The forward implication of `odg:def:thm:ce`, including its order-free
characteristic-zero extension. The only ring-specific input is the actual
integer-valued constant-term retraction.
-/

namespace Surreal.HahnSeries
noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [CharZero K] {n : ℕ}
local notation "A" => coefficientRestrictedSubring (Γ := Γ) (Int.castRingHom K)

/-- Integer traces of finite-system Diophantine sets are computably enumerable. -/
theorem integerRestricted_diophantine_trace_re {D : Set (Fin n → A)}
    (hD : IntegerDiophantine.Definable D) :
    REPred (fun x : Fin n → ℤ => (fun j => (x j : A)) ∈ D) :=
  hD.integer_trace_re
    (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom K) Int.cast_injective)

/-- A Diophantine subset supported on standard integer tuples is computably enumerable. -/
theorem integerRestricted_standard_diophantine_re {D : Set (Fin n → ℤ)}
    (hD : IntegerDiophantine.Definable (IntegerDiophantine.standardImage D : Set (Fin n → A))) :
    REPred (· ∈ D) :=
  hD.standardImage_re
    (coefficientRestrictedRetraction (Γ := Γ) (Int.castRingHom K) Int.cast_injective)

end
end Surreal.HahnSeries
