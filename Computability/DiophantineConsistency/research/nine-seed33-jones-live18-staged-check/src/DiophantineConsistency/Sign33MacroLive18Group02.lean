import DiophantineConsistency.Sign33MacroRankSymbolic

/-! Candidate d18 live-entry carries; no final recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroLive18
open Sign33MacroLanguage Sign33MacroPrefixes

theorem d18_G_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a ((Fin.last 9).castSucc) := by
  calc
    d18.values a ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d17.values a ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d17 _ ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d16.values a ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d16 _).values a (Fin.castSucc ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d16 _ ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d15.values a ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d15 _).values a (Fin.castSucc ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d15 _ ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d14.values a ((Fin.last 9).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d14 _).values a (Fin.castSucc ((Fin.last 9).castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d14 _ ((Fin.last 9).castSucc.castSucc.castSucc.castSucc)
    _ = d13.values a ((Fin.last 9).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d13 _).values a (Fin.castSucc ((Fin.last 9).castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d13 _ ((Fin.last 9).castSucc.castSucc.castSucc)
    _ = d12.values a ((Fin.last 9).castSucc.castSucc) := by
      change (Dag.snoc d12 _).values a (Fin.castSucc ((Fin.last 9).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d12 _ ((Fin.last 9).castSucc.castSucc)
    _ = d11.values a ((Fin.last 9).castSucc) := by
      change (Dag.snoc d11 _).values a (Fin.castSucc ((Fin.last 9).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d11 _ ((Fin.last 9).castSucc)

theorem d18_R_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a ((Fin.last 10)) := by
  calc
    d18.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d17.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d17 _ ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d16.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d16 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d16 _ ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d15.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d15 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d15 _ ((Fin.last 10).castSucc.castSucc.castSucc.castSucc)
    _ = d14.values a ((Fin.last 10).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d14 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d14 _ ((Fin.last 10).castSucc.castSucc.castSucc)
    _ = d13.values a ((Fin.last 10).castSucc.castSucc) := by
      change (Dag.snoc d13 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d13 _ ((Fin.last 10).castSucc.castSucc)
    _ = d12.values a ((Fin.last 10).castSucc) := by
      change (Dag.snoc d12 _).values a (Fin.castSucc ((Fin.last 10).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d12 _ ((Fin.last 10).castSucc)
    _ = d11.values a ((Fin.last 10)) := by
      change (Dag.snoc d11 _).values a (Fin.castSucc ((Fin.last 10))) = _
      exact Sign33MacroCuts.snoc_previous a d11 _ ((Fin.last 10))

theorem d18_h_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d12.values a ((Fin.last 11)) := by
  calc
    d18.values a ((Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d17.values a ((Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ((Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d17 _ ((Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d16.values a ((Fin.last 11).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d16 _).values a (Fin.castSucc ((Fin.last 11).castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d16 _ ((Fin.last 11).castSucc.castSucc.castSucc.castSucc)
    _ = d15.values a ((Fin.last 11).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d15 _).values a (Fin.castSucc ((Fin.last 11).castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d15 _ ((Fin.last 11).castSucc.castSucc.castSucc)
    _ = d14.values a ((Fin.last 11).castSucc.castSucc) := by
      change (Dag.snoc d14 _).values a (Fin.castSucc ((Fin.last 11).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d14 _ ((Fin.last 11).castSucc.castSucc)
    _ = d13.values a ((Fin.last 11).castSucc) := by
      change (Dag.snoc d13 _).values a (Fin.castSucc ((Fin.last 11).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d13 _ ((Fin.last 11).castSucc)
    _ = d12.values a ((Fin.last 11)) := by
      change (Dag.snoc d12 _).values a (Fin.castSucc ((Fin.last 11))) = _
      exact Sign33MacroCuts.snoc_previous a d12 _ ((Fin.last 11))

#print axioms d18_G_carry
#print axioms d18_R_carry
#print axioms d18_h_carry
end DiophantineConsistency.Sign33MacroLive18
