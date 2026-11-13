import DiophantineConsistency.Norm38MacroDependentBprime

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent03
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d25_b_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d25.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d18.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d25.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d24.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d24 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d24 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d23.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d23 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d23 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d22.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d22 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d22 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d21.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d21 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d21 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d20.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d20 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d20 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d19.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d19 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d19 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d18.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d18 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d18 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem d25_w_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d25.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d18.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc) := by
  calc
    d25.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d24.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d24 _).values a (Fin.castSucc ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d24 _ ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d23.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d23 _).values a (Fin.castSucc ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d23 _ ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d22.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d22 _).values a (Fin.castSucc ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d22 _ ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d21.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d21 _).values a (Fin.castSucc ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d21 _ ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d20.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d20 _).values a (Fin.castSucc ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d20 _ ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d19.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d19 _).values a (Fin.castSucc ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d19 _ ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d18.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d18 _).values a (Fin.castSucc ((Fin.last 13).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d18 _ ((Fin.last 13).castSucc.castSucc.castSucc.castSucc)

theorem prefix_W {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d26.values a (Fin.last 25) = d25.values a ⟨0, by decide⟩ *
      d25.values a ⟨13, by decide⟩ := by
  rw [d26, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d25_b_carry
#print axioms d25_w_carry
#print axioms prefix_W
end DiophantineConsistency.Norm38MacroDependent03
