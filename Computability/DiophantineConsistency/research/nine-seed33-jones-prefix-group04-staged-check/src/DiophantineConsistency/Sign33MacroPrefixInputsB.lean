import DiophantineConsistency.Sign33MacroPrefixGlarge

/-! Candidate phi/i/j/t short-prefix values; prior nodes remain opaque. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPrefixGroup04
open Sign33MacroLanguage Sign33MacroPrefixes

theorem prefix_phi {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d15.values a (Fin.last 14) = a ⟨5, by decide⟩ := by
  rw [d15, Sign33MacroCuts.snoc_last]
  rfl

theorem prefix_i {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d16.values a (Fin.last 15) = a ⟨6, by decide⟩ + ((1 : Int) : R) := by
  rw [d16, Sign33MacroCuts.snoc_last]
  rfl

theorem prefix_j {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d17.values a (Fin.last 16) = a ⟨7, by decide⟩ + ((1 : Int) : R) := by
  rw [d17, Sign33MacroCuts.snoc_last]
  rfl

theorem prefix_t {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a (Fin.last 17) = a ⟨8, by decide⟩ := by
  rw [d18, Sign33MacroCuts.snoc_last]
  rfl

#print axioms prefix_phi
#print axioms prefix_i
#print axioms prefix_j
#print axioms prefix_t
end DiophantineConsistency.Sign33MacroPrefixGroup04
