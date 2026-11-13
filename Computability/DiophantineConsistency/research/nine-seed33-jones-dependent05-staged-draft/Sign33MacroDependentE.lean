import DiophantineConsistency.Sign33MacroDependentIcarry

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroDependent05
open Sign33MacroLanguage Sign33MacroPrefixes

theorem d30_i_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d30.values a ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d24.values a ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d30.values a ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d29.values a ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d29 _ ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d28.values a ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d28 _ ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d27.values a ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d27 _ ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d26.values a ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d26 _).values a (Fin.castSucc ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d26 _ ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d25.values a ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d25 _).values a (Fin.castSucc ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d25 _ ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d24.values a ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d24 _).values a (Fin.castSucc ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d24 _ ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem d30_J_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d30.values a ((Fin.last 27).castSucc.castSucc) = d28.values a ((Fin.last 27)) := by
  calc
    d30.values a ((Fin.last 27).castSucc.castSucc) =
        d29.values a ((Fin.last 27).castSucc) := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ((Fin.last 27).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d29 _ ((Fin.last 27).castSucc)
    _ = d28.values a ((Fin.last 27)) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 27))) = _
      exact Sign33MacroCuts.snoc_previous a d28 _ ((Fin.last 27))

theorem d30_C_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d30.values a ((Fin.last 26).castSucc.castSucc.castSucc) = d27.values a ((Fin.last 26)) := by
  calc
    d30.values a ((Fin.last 26).castSucc.castSucc.castSucc) =
        d29.values a ((Fin.last 26).castSucc.castSucc) := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ((Fin.last 26).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d29 _ ((Fin.last 26).castSucc.castSucc)
    _ = d28.values a ((Fin.last 26).castSucc) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 26).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d28 _ ((Fin.last 26).castSucc)
    _ = d27.values a ((Fin.last 26)) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 26))) = _
      exact Sign33MacroCuts.snoc_previous a d27 _ ((Fin.last 26))

theorem prefix_E {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d31.values a (Fin.last 30) = d30.values a ⟨15, by decide⟩ * d30.values a ⟨27, by decide⟩ *
      d30.values a ⟨29, by decide⟩ * (d30.values a ⟨26, by decide⟩) ^ (2 : Nat) := by
  rw [d31, Sign33MacroCuts.snoc_last]
  rfl

#print axioms d30_i_carry
#print axioms d30_J_carry
#print axioms d30_C_carry
#print axioms prefix_E
end DiophantineConsistency.Sign33MacroDependent05
