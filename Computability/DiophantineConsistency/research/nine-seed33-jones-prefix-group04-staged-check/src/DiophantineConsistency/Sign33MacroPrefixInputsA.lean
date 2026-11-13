import DiophantineConsistency.Sign33MacroPrefixGlarge

/-! Candidate h/s/w short-prefix values; prior nodes remain opaque. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixGroup04
open Sign33MacroLanguage Sign33MacroPrefixes

theorem prefix_h {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d12.values a (Fin.last 11) = a ⟨2, by decide⟩ + ((1 : Int) : R) := by
  rw [d12, Sign33MacroCuts.snoc_last]
  rfl

theorem prefix_s {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d13.values a (Fin.last 12) = a ⟨3, by decide⟩ + ((1 : Int) : R) := by
  rw [d13, Sign33MacroCuts.snoc_last]
  rfl

theorem prefix_w {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d14.values a (Fin.last 13) = a ⟨4, by decide⟩ + ((1 : Int) : R) := by
  rw [d14, Sign33MacroCuts.snoc_last]
  rfl

#print axioms prefix_h
#print axioms prefix_s
#print axioms prefix_w
end DiophantineConsistency.Sign33MacroPrefixGroup04
