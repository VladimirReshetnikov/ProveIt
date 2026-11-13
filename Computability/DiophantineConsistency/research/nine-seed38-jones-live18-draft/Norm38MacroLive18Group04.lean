import DiophantineConsistency.Norm38MacroRankSymbolic

/-! Candidate d18 live-entry carries; no final recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroLive18
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d18_i_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 15).castSucc.castSucc) = d16.values a ((Fin.last 15)) := by
  calc
    d18.values a ((Fin.last 15).castSucc.castSucc) =
        d17.values a ((Fin.last 15).castSucc) := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ((Fin.last 15).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d17 _ ((Fin.last 15).castSucc)
    _ = d16.values a ((Fin.last 15)) := by
      change (Dag.snoc d16 _).values a (Fin.castSucc ((Fin.last 15))) = _
      exact Norm38MacroCuts.snoc_previous a d16 _ ((Fin.last 15))

theorem d18_j_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 16).castSucc) = d17.values a ((Fin.last 16)) := by
  calc
    d18.values a ((Fin.last 16).castSucc) =
        d17.values a ((Fin.last 16)) := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ((Fin.last 16))) = _
      exact Norm38MacroCuts.snoc_previous a d17 _ ((Fin.last 16))

#print axioms d18_i_carry
#print axioms d18_j_carry
end DiophantineConsistency.Norm38MacroLive18
