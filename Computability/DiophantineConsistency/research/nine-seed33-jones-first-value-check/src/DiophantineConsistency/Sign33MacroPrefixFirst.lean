import DiophantineConsistency.Sign33MacroPrefixes
import DiophantineConsistency.Sign33MacroCuts

/-! Source-only first named-prefix value; no full-recipe value claim. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixFirst
open Sign33MacroLanguage Sign33MacroPrefixes ExecutableJones

theorem first_prefix_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d1.values a (Fin.last 0) =
      ((indexY Sign33MacroLanguage.seed 0 : Nat) : R) + ((1 : Int) : R) + a ⟨0, by decide⟩ := by
  rw [d1, Sign33MacroCuts.snoc_last]
  rfl

#print axioms first_prefix_value
end DiophantineConsistency.Sign33MacroPrefixFirst
