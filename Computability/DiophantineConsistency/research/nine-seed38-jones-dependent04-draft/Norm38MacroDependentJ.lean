import DiophantineConsistency.Norm38MacroDependentC

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent04
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d27_A_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d27.values a ((Fin.last 23).castSucc.castSucc.castSucc) = d24.values a ((Fin.last 23)) := by
  calc
    d27.values a ((Fin.last 23).castSucc.castSucc.castSucc) =
        d26.values a ((Fin.last 23).castSucc.castSucc) := by
      change (Dag.snoc d26 _).values a (Fin.castSucc ((Fin.last 23).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d26 _ ((Fin.last 23).castSucc.castSucc)
    _ = d25.values a ((Fin.last 23).castSucc) := by
      change (Dag.snoc d25 _).values a (Fin.castSucc ((Fin.last 23).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d25 _ ((Fin.last 23).castSucc)
    _ = d24.values a ((Fin.last 23)) := by
      change (Dag.snoc d24 _).values a (Fin.castSucc ((Fin.last 23))) = _
      exact Norm38MacroCuts.snoc_previous a d24 _ ((Fin.last 23))

theorem prefix_J {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d28.values a (Fin.last 27) = ((4 : Int) : R) *
      d27.values a ⟨23, by decide⟩ - ((5 : Int) : R) := by
  rw [d28, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d27_A_carry
#print axioms prefix_J
end DiophantineConsistency.Norm38MacroDependent04
