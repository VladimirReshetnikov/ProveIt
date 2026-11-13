import DiophantineConsistency.Norm38MacroPrefixGlarge

/-! Candidate h/s/w short-prefix values; prior nodes remain opaque. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPrefixGroup04
open Norm38MacroLanguage Norm38MacroPrefixes

theorem prefix_h {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d12.values a (Fin.last 11) = a ⟨2, by decide⟩ + ((1 : Int) : R) := by
  rw [d12, Norm38MacroCuts.snoc_last]
  rfl

theorem prefix_s {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d13.values a (Fin.last 12) = a ⟨3, by decide⟩ + ((1 : Int) : R) := by
  rw [d13, Norm38MacroCuts.snoc_last]
  rfl

theorem prefix_w {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d14.values a (Fin.last 13) = a ⟨4, by decide⟩ + ((1 : Int) : R) := by
  rw [d14, Norm38MacroCuts.snoc_last]
  rfl

#print axioms prefix_h
#print axioms prefix_s
#print axioms prefix_w
end DiophantineConsistency.Norm38MacroPrefixGroup04
