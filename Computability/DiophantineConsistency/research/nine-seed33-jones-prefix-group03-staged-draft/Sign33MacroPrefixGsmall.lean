import DiophantineConsistency.Sign33MacroPrefixCarry03

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixGroup03
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01 Sign33MacroPrefixGroup02 ExecutableJones

theorem prefix_g {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d8.values a (Fin.last 7) = a ⟨1, by decide⟩ + ((1 : Int) : R) := by
  rw [d8, Sign33MacroCuts.snoc_last]
  rfl

#print axioms prefix_g
end DiophantineConsistency.Sign33MacroPrefixGroup03
