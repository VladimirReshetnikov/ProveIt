import DiophantineConsistency.Sign33MacroDependentU

/-! Candidate short-prefix Y evaluator; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroDependent01
open Sign33MacroLanguage Sign33MacroPrefixes

theorem prefix_Y {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d20.values a (Fin.last 19) = (d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) ^ (2 : Nat) *
      d18.values a ((Fin.last 12).castSucc.castSucc.castSucc.castSucc.castSucc) := by
  rw [d20, Sign33MacroCuts.snoc_last]
  change (d19.values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))) ^ (2 : Nat) *
    d19.values a (Fin.castSucc ((Fin.last 12).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
  have hN : d19.values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
    change (Dag.snoc d18 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
    exact Sign33MacroCuts.snoc_previous a d18 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
  have hs : d19.values a (Fin.castSucc ((Fin.last 12).castSucc.castSucc.castSucc.castSucc.castSucc)) = d18.values a ((Fin.last 12).castSucc.castSucc.castSucc.castSucc.castSucc) := by
    change (Dag.snoc d18 _).values a (Fin.castSucc ((Fin.last 12).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
    exact Sign33MacroCuts.snoc_previous a d18 _ ((Fin.last 12).castSucc.castSucc.castSucc.castSucc.castSucc)
  rw [hN, hs]

#print axioms prefix_Y
end DiophantineConsistency.Sign33MacroDependent01
