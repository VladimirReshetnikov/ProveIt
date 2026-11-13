import DiophantineConsistency.Sign33MacroDependentV

/-! Candidate local last-entry identities; no composed semantics theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroDependent08
open Sign33MacroLanguage Sign33MacroPrefixes

theorem prefix_Bd {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d40.values a (Fin.last 39) = (d39.values a ⟨27, by decide⟩ * d39.values a ⟨31, by decide⟩) ^ (2 : Nat) := by
  rw [d40, Sign33MacroCuts.snoc_last]
  rfl

theorem prefix_Cd {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a (Fin.last 40) = (d40.values a ⟨28, by decide⟩ * d40.values a ⟨31, by decide⟩ +
      d40.values a ⟨27, by decide⟩ * (d40.values a ⟨33, by decide⟩ - d40.values a ⟨26, by decide⟩)) ^ (2 : Nat) := by
  rw [d41, Sign33MacroCuts.snoc_last]
  rfl

#print axioms prefix_Bd
#print axioms prefix_Cd
end DiophantineConsistency.Sign33MacroDependent08
