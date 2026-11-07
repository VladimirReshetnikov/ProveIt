import DiophantineConsistency.Sign33MacroDependentHcarry

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroDependent06
open Sign33MacroLanguage Sign33MacroPrefixes

theorem d33_C_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d33.values a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d27.values a ((Fin.last 26)) := by
  calc
    d33.values a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d32.values a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d32 _).values a (Fin.castSucc ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d32 _ ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d31.values a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d31 _).values a (Fin.castSucc ((Fin.last 26).castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d31 _ ((Fin.last 26).castSucc.castSucc.castSucc.castSucc)
    _ = d30.values a ((Fin.last 26).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d30 _).values a (Fin.castSucc ((Fin.last 26).castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d30 _ ((Fin.last 26).castSucc.castSucc.castSucc)
    _ = d29.values a ((Fin.last 26).castSucc.castSucc) := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ((Fin.last 26).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d29 _ ((Fin.last 26).castSucc.castSucc)
    _ = d28.values a ((Fin.last 26).castSucc) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 26).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d28 _ ((Fin.last 26).castSucc)
    _ = d27.values a ((Fin.last 26)) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 26))) = _
      exact Sign33MacroCuts.snoc_previous a d27 _ ((Fin.last 26))

theorem prefix_H {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d34.values a (Fin.last 33) = d33.values a ⟨24, by decide⟩ +
      d33.values a ⟨16, by decide⟩ * d33.values a ⟨26, by decide⟩ := by
  rw [d34, Sign33MacroCuts.snoc_last]
  rfl

#print axioms d33_C_carry
#print axioms prefix_H
end DiophantineConsistency.Sign33MacroDependent06
