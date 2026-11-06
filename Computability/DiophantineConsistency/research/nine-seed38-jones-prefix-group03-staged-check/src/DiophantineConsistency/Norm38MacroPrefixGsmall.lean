import DiophantineConsistency.Norm38MacroPrefixCarry03

/-! Mechanical source split; Lean result not implied. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup03
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01 Norm38MacroPrefixGroup02 ExecutableJones

theorem prefix_g {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d8.values a (Fin.last 7) = a ⟨1, by decide⟩ + ((1 : Int) : R) := by
  rw [d8, Norm38MacroCuts.snoc_last]
  rfl

#print axioms prefix_g
end DiophantineConsistency.Norm38MacroPrefixGroup03
