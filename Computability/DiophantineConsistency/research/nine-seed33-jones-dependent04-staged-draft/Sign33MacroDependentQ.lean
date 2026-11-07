import DiophantineConsistency.Sign33MacroDependentJ

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroDependent04
open Sign33MacroLanguage Sign33MacroPrefixes

theorem d28_W_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d28.values a ((Fin.last 25).castSucc.castSucc) = d26.values a ((Fin.last 25)) := by
  calc
    d28.values a ((Fin.last 25).castSucc.castSucc) =
        d27.values a ((Fin.last 25).castSucc) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 25).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d27 _ ((Fin.last 25).castSucc)
    _ = d26.values a ((Fin.last 25)) := by
      change (Dag.snoc d26 _).values a (Fin.castSucc ((Fin.last 25))) = _
      exact Sign33MacroCuts.snoc_previous a d26 _ ((Fin.last 25))

theorem d28_C_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d28.values a ((Fin.last 26).castSucc) = d27.values a ((Fin.last 26)) := by
  calc
    d28.values a ((Fin.last 26).castSucc) =
        d27.values a ((Fin.last 26)) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 26))) = _
      exact Sign33MacroCuts.snoc_previous a d27 _ ((Fin.last 26))

theorem prefix_Q {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d29.values a (Fin.last 28) = ((3 : Int) : R) * d28.values a ⟨25, by decide⟩ *
      d28.values a ⟨26, by decide⟩ - ((2 : Int) : R) *
        ((d28.values a ⟨25, by decide⟩) ^ (2 : Nat) - ((1 : Int) : R)) := by
  rw [d29, Sign33MacroCuts.snoc_last]
  rfl

#print axioms d28_W_carry
#print axioms d28_C_carry
#print axioms prefix_Q
end DiophantineConsistency.Sign33MacroDependent04
