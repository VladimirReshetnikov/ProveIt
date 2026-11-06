import DiophantineConsistency.Norm38MacroDependentA

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent03
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d24_R_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d24.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d18.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d24.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d23.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d23 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d23 _ ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d22.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d22 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d22 _ ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d21.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d21 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d21 _ ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d20.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d20 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d20 _ ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d19.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d19 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d19 _ ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d18.values a ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d18 _).values a (Fin.castSucc ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d18 _ ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)

theorem prefix_Bprime {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d25.values a (Fin.last 24) = ((2 : Int) : R) *
      d24.values a ⟨10, by decide⟩ + ((1 : Int) : R) := by
  rw [d25, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d24_R_carry
#print axioms prefix_Bprime
end DiophantineConsistency.Norm38MacroDependent03
