import DiophantineConsistency.Sign33MacroDependentA0Early

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroDependent07
open Sign33MacroLanguage Sign33MacroPrefixes

theorem d35_P_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d35.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d28.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d35.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d34.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d34 _).values a (Fin.castSucc ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d34 _ ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d33.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d33 _).values a (Fin.castSucc ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d33 _ ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d32.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d32 _).values a (Fin.castSucc ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d32 _ ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d31.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d31 _).values a (Fin.castSucc ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d31 _ ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d30.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d30 _).values a (Fin.castSucc ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d30 _ ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d29.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d29 _ ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d28.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d28 _ ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem d35_K_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d35.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d29.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d35.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d34.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d34 _).values a (Fin.castSucc ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d34 _ ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d33.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d33 _).values a (Fin.castSucc ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d33 _ ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d32.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d32 _).values a (Fin.castSucc ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d32 _ ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d31.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d31 _).values a (Fin.castSucc ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d31 _ ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d30.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d30 _).values a (Fin.castSucc ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d30 _ ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d29.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d29 _ ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem prefix_A0 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d36.values a (Fin.last 35) = ((d35.values a ⟨21, by decide⟩) ^ (2 : Nat) - ((1 : Int) : R)) *
      (d35.values a ⟨22, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R) := by
  rw [d36, Sign33MacroCuts.snoc_last]
  rfl

#print axioms d35_P_carry
#print axioms d35_K_carry
#print axioms prefix_A0
end DiophantineConsistency.Sign33MacroDependent07
