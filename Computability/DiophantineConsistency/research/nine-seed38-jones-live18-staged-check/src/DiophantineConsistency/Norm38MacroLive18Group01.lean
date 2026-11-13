import DiophantineConsistency.Norm38MacroRankSymbolic

/-! Candidate d18 live-entry carries; no final recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroLive18
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d18_b_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d18.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d17.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d17 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d16.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d16 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d16 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d15.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d15 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d15 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d14.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d14 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d14 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d13.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d13 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d13 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d12.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d12 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d12 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d11.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d11 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d11 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem d18_N_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d17.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d17 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d16.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d16 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d16 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d15.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d15 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d15 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d14.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d14 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d14 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d13.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d13 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d13 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d12.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d12 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d12 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d11.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d11 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d11 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem d18_g_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a ((Fin.last 7).castSucc.castSucc.castSucc) := by
  calc
    d18.values a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d17.values a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d17 _ ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d16.values a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d16 _).values a (Fin.castSucc ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d16 _ ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d15.values a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d15 _).values a (Fin.castSucc ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d15 _ ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d14.values a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d14 _).values a (Fin.castSucc ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d14 _ ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d13.values a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d13 _).values a (Fin.castSucc ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d13 _ ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d12.values a ((Fin.last 7).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d12 _).values a (Fin.castSucc ((Fin.last 7).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d12 _ ((Fin.last 7).castSucc.castSucc.castSucc.castSucc)
    _ = d11.values a ((Fin.last 7).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d11 _).values a (Fin.castSucc ((Fin.last 7).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d11 _ ((Fin.last 7).castSucc.castSucc.castSucc)

#print axioms d18_b_carry
#print axioms d18_N_carry
#print axioms d18_g_carry
end DiophantineConsistency.Norm38MacroLive18
