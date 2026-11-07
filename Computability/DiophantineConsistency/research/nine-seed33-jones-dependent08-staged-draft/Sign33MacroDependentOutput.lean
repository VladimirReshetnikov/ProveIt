import DiophantineConsistency.Sign33MacroDependentDmKc

/-! Candidate local last-entry identities; no composed semantics theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroDependent08
open Sign33MacroLanguage Sign33MacroPrefixes

theorem prefix_T {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d44.values a (Fin.last 43) = d43.values a ⟨39, by decide⟩ * d43.values a ⟨17, by decide⟩ +
      d43.values a ⟨40, by decide⟩ - d43.values a ⟨42, by decide⟩ *
        (d43.values a ⟨40, by decide⟩ + d43.values a ⟨37, by decide⟩ * d43.values a ⟨38, by decide⟩) := by
  rw [d44, Sign33MacroCuts.snoc_last]
  rfl

theorem prefix_output {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d45.values a (Fin.last 44) =
      ((d44.values a ⟨43, by decide⟩) ^ (2 : Nat) +
        (d44.values a ⟨42, by decide⟩) ^ (2 : Nat) * d44.values a ⟨35, by decide⟩ -
        (d44.values a ⟨42, by decide⟩) ^ (2 : Nat) * (d44.values a ⟨37, by decide⟩) ^ (2 : Nat) *
          d44.values a ⟨36, by decide⟩) ^ (2 : Nat) -
        ((4 : Int) : R) * (d44.values a ⟨43, by decide⟩) ^ (2 : Nat) *
          (d44.values a ⟨42, by decide⟩) ^ (2 : Nat) * d44.values a ⟨35, by decide⟩ := by
  rw [d45, Sign33MacroCuts.snoc_last]
  rfl

#print axioms prefix_T
#print axioms prefix_output
end DiophantineConsistency.Sign33MacroDependent08
