import DiophantineConsistency.Norm38MacroPrefixes
import DiophantineConsistency.Norm38MacroCuts

/-! Source-only first named-prefix value; no full-recipe value claim. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixFirst
open Norm38MacroLanguage Norm38MacroPrefixes ExecutableJones

theorem first_prefix_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d1.values a (Fin.last 0) =
      ((indexY Norm38MacroLanguage.seed 0 : Nat) : R) + ((1 : Int) : R) + a ⟨0, by decide⟩ := by
  rw [d1, Norm38MacroCuts.snoc_last]
  rfl

#print axioms first_prefix_value
end DiophantineConsistency.Norm38MacroPrefixFirst
