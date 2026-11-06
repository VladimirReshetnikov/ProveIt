import DiophantineConsistency.Norm38MacroDependentQ

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent04
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d29_A_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d29.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc) = d24.values a ((Fin.last 23)) := by
  calc
    d29.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc) =
        d28.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 23).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d28 _ ((Fin.last 23).castSucc.castSucc.castSucc.castSucc)
    _ = d27.values a ((Fin.last 23).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 23).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d27 _ ((Fin.last 23).castSucc.castSucc.castSucc)
    _ = d26.values a ((Fin.last 23).castSucc.castSucc) := by
      change (Dag.snoc d26 _).values a (Fin.castSucc ((Fin.last 23).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d26 _ ((Fin.last 23).castSucc.castSucc)
    _ = d25.values a ((Fin.last 23).castSucc) := by
      change (Dag.snoc d25 _).values a (Fin.castSucc ((Fin.last 23).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d25 _ ((Fin.last 23).castSucc)
    _ = d24.values a ((Fin.last 23)) := by
      change (Dag.snoc d24 _).values a (Fin.castSucc ((Fin.last 23))) = _
      exact Norm38MacroCuts.snoc_previous a d24 _ ((Fin.last 23))

theorem d29_C_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d29.values a ((Fin.last 26).castSucc.castSucc) = d27.values a ((Fin.last 26)) := by
  calc
    d29.values a ((Fin.last 26).castSucc.castSucc) =
        d28.values a ((Fin.last 26).castSucc) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 26).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d28 _ ((Fin.last 26).castSucc)
    _ = d27.values a ((Fin.last 26)) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 26))) = _
      exact Norm38MacroCuts.snoc_previous a d27 _ ((Fin.last 26))

theorem prefix_D {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d30.values a (Fin.last 29) = ((d29.values a ⟨23, by decide⟩) ^ (2 : Nat) - ((1 : Int) : R)) *
      (d29.values a ⟨26, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R) := by
  rw [d30, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d29_A_carry
#print axioms d29_C_carry
#print axioms prefix_D
end DiophantineConsistency.Norm38MacroDependent04
