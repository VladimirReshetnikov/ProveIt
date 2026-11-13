import DiophantineConsistency.Norm38MacroDependentY

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent02
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d20_R_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d20.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d18.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d20.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d19.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d19 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d19 _ ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d18.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d18 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d18 _ ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem prefix_M {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d21.values a (Fin.last 20) = d20.values a ⟨10, by decide⟩ *
      d20.values a ⟨19, by decide⟩ := by
  rw [d21, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d20_R_carry
#print axioms prefix_M
end DiophantineConsistency.Norm38MacroDependent02
