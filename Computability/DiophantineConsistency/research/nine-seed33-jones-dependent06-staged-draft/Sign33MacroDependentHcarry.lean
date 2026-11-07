import DiophantineConsistency.Sign33MacroDependentGprime

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroDependent06
open Sign33MacroLanguage Sign33MacroPrefixes

theorem d33_j_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d33.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d25.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d33.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d32.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d32 _).values a (Fin.castSucc ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d32 _ ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d31.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d31 _).values a (Fin.castSucc ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d31 _ ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d30.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d30 _).values a (Fin.castSucc ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d30 _ ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d29.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d29 _ ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d28.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d28 _ ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d27.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d27 _ ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d26.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d26 _).values a (Fin.castSucc ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d26 _ ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d25.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d25 _).values a (Fin.castSucc ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d25 _ ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem d33_Bprime_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d33.values a ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d25.values a ((Fin.last 24)) := by
  calc
    d33.values a ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d32.values a ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d32 _).values a (Fin.castSucc ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d32 _ ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d31.values a ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d31 _).values a (Fin.castSucc ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d31 _ ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d30.values a ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d30 _).values a (Fin.castSucc ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d30 _ ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d29.values a ((Fin.last 24).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ((Fin.last 24).castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d29 _ ((Fin.last 24).castSucc.castSucc.castSucc.castSucc)
    _ = d28.values a ((Fin.last 24).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 24).castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d28 _ ((Fin.last 24).castSucc.castSucc.castSucc)
    _ = d27.values a ((Fin.last 24).castSucc.castSucc) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 24).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d27 _ ((Fin.last 24).castSucc.castSucc)
    _ = d26.values a ((Fin.last 24).castSucc) := by
      change (Dag.snoc d26 _).values a (Fin.castSucc ((Fin.last 24).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d26 _ ((Fin.last 24).castSucc)
    _ = d25.values a ((Fin.last 24)) := by
      change (Dag.snoc d25 _).values a (Fin.castSucc ((Fin.last 24))) = _
      exact Sign33MacroCuts.snoc_previous a d25 _ ((Fin.last 24))


#print axioms d33_j_carry
#print axioms d33_Bprime_carry
end DiophantineConsistency.Sign33MacroDependent06
