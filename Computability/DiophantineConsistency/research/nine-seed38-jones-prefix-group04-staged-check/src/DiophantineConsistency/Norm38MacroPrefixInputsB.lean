import DiophantineConsistency.Norm38MacroPrefixGlarge

/-! Candidate phi/i/j/t short-prefix values; prior nodes remain opaque. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup04
open Norm38MacroLanguage Norm38MacroPrefixes

theorem prefix_phi {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d15.values a (Fin.last 14) = a ⟨5, by decide⟩ := by
  rw [d15, Norm38MacroCuts.snoc_last]
  rfl

theorem prefix_i {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d16.values a (Fin.last 15) = a ⟨6, by decide⟩ + ((1 : Int) : R) := by
  rw [d16, Norm38MacroCuts.snoc_last]
  rfl

theorem prefix_j {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d17.values a (Fin.last 16) = a ⟨7, by decide⟩ + ((1 : Int) : R) := by
  rw [d17, Norm38MacroCuts.snoc_last]
  rfl

theorem prefix_t {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a (Fin.last 17) = a ⟨8, by decide⟩ := by
  rw [d18, Norm38MacroCuts.snoc_last]
  rfl

#print axioms prefix_phi
#print axioms prefix_i
#print axioms prefix_j
#print axioms prefix_t
end DiophantineConsistency.Norm38MacroPrefixGroup04
