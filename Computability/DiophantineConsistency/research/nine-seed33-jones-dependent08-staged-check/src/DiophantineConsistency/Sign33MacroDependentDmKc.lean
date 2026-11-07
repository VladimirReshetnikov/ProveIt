import DiophantineConsistency.Sign33MacroDependentBdCd

/-! Candidate local last-entry identities; no composed semantics theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroDependent08
open Sign33MacroLanguage Sign33MacroPrefixes

theorem prefix_Dm {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d42.values a (Fin.last 41) = (d41.values a ⟨22, by decide⟩) ^ (2 : Nat) * d41.values a ⟨9, by decide⟩ -
      ((4 : Int) : R) * (d41.values a ⟨26, by decide⟩ - d41.values a ⟨22, by decide⟩ *
        d41.values a ⟨19, by decide⟩) ^ (2 : Nat) * d41.values a ⟨9, by decide⟩ -
      ((8 : Int) : R) * d41.values a ⟨7, by decide⟩ * (d41.values a ⟨22, by decide⟩) ^ (2 : Nat) := by
  rw [d42, Sign33MacroCuts.snoc_last]
  rfl

theorem prefix_Kc {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d43.values a (Fin.last 42) = d42.values a ⟨39, by decide⟩ *
      (((2 : Int) : R) * d42.values a ⟨41, by decide⟩ - ((1 : Int) : R)) := by
  rw [d43, Sign33MacroCuts.snoc_last]
  rfl

#print axioms prefix_Dm
#print axioms prefix_Kc
end DiophantineConsistency.Sign33MacroDependent08
