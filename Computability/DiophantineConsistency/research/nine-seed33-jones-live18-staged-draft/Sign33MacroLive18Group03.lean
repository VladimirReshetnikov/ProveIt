import DiophantineConsistency.Sign33MacroRankSymbolic

/-! Candidate d18 live-entry carries; no final recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroLive18
open Sign33MacroLanguage Sign33MacroPrefixes

theorem d18_s_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 12).castSucc.castSucc.castSucc.castSucc.castSucc) = d13.values a ((Fin.last 12)) := by
  calc
    d18.values a ((Fin.last 12).castSucc.castSucc.castSucc.castSucc.castSucc) =
        d17.values a ((Fin.last 12).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ((Fin.last 12).castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d17 _ ((Fin.last 12).castSucc.castSucc.castSucc.castSucc)
    _ = d16.values a ((Fin.last 12).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d16 _).values a (Fin.castSucc ((Fin.last 12).castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d16 _ ((Fin.last 12).castSucc.castSucc.castSucc)
    _ = d15.values a ((Fin.last 12).castSucc.castSucc) := by
      change (Dag.snoc d15 _).values a (Fin.castSucc ((Fin.last 12).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d15 _ ((Fin.last 12).castSucc.castSucc)
    _ = d14.values a ((Fin.last 12).castSucc) := by
      change (Dag.snoc d14 _).values a (Fin.castSucc ((Fin.last 12).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d14 _ ((Fin.last 12).castSucc)
    _ = d13.values a ((Fin.last 12)) := by
      change (Dag.snoc d13 _).values a (Fin.castSucc ((Fin.last 12))) = _
      exact Sign33MacroCuts.snoc_previous a d13 _ ((Fin.last 12))

theorem d18_w_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc) = d14.values a ((Fin.last 13)) := by
  calc
    d18.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc) =
        d17.values a ((Fin.last 13).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ((Fin.last 13).castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d17 _ ((Fin.last 13).castSucc.castSucc.castSucc)
    _ = d16.values a ((Fin.last 13).castSucc.castSucc) := by
      change (Dag.snoc d16 _).values a (Fin.castSucc ((Fin.last 13).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d16 _ ((Fin.last 13).castSucc.castSucc)
    _ = d15.values a ((Fin.last 13).castSucc) := by
      change (Dag.snoc d15 _).values a (Fin.castSucc ((Fin.last 13).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d15 _ ((Fin.last 13).castSucc)
    _ = d14.values a ((Fin.last 13)) := by
      change (Dag.snoc d14 _).values a (Fin.castSucc ((Fin.last 13))) = _
      exact Sign33MacroCuts.snoc_previous a d14 _ ((Fin.last 13))

theorem d18_phi_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 14).castSucc.castSucc.castSucc) = d15.values a ((Fin.last 14)) := by
  calc
    d18.values a ((Fin.last 14).castSucc.castSucc.castSucc) =
        d17.values a ((Fin.last 14).castSucc.castSucc) := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ((Fin.last 14).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d17 _ ((Fin.last 14).castSucc.castSucc)
    _ = d16.values a ((Fin.last 14).castSucc) := by
      change (Dag.snoc d16 _).values a (Fin.castSucc ((Fin.last 14).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d16 _ ((Fin.last 14).castSucc)
    _ = d15.values a ((Fin.last 14)) := by
      change (Dag.snoc d15 _).values a (Fin.castSucc ((Fin.last 14))) = _
      exact Sign33MacroCuts.snoc_previous a d15 _ ((Fin.last 14))

#print axioms d18_s_carry
#print axioms d18_w_carry
#print axioms d18_phi_carry
end DiophantineConsistency.Sign33MacroLive18
