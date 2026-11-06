import DiophantineConsistency.Norm38MacroDependentV

/-! Candidate local last-entry identities; no composed semantics theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent08
open Norm38MacroLanguage Norm38MacroPrefixes

theorem prefix_Bd {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d40.values a (Fin.last 39) = (d39.values a ⟨27, by decide⟩ * d39.values a ⟨31, by decide⟩) ^ (2 : Nat) := by
  rw [d40, Norm38MacroCuts.snoc_last]
  rfl

theorem prefix_Cd {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a (Fin.last 40) = (d40.values a ⟨28, by decide⟩ * d40.values a ⟨31, by decide⟩ +
      d40.values a ⟨27, by decide⟩ * (d40.values a ⟨33, by decide⟩ - d40.values a ⟨26, by decide⟩)) ^ (2 : Nat) := by
  rw [d41, Norm38MacroCuts.snoc_last]
  rfl

#print axioms prefix_Bd
#print axioms prefix_Cd
end DiophantineConsistency.Norm38MacroDependent08
