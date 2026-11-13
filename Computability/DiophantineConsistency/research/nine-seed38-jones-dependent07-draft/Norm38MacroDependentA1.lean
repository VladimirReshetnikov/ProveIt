import DiophantineConsistency.Norm38MacroDependentA0

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent07
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d36_D_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d36.values a ((Fin.last 29).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d30.values a ((Fin.last 29)) := by
  calc
    d36.values a ((Fin.last 29).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d35.values a ((Fin.last 29).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d35 _).values a (Fin.castSucc ((Fin.last 29).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d35 _ ((Fin.last 29).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d34.values a ((Fin.last 29).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d34 _).values a (Fin.castSucc ((Fin.last 29).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d34 _ ((Fin.last 29).castSucc.castSucc.castSucc.castSucc)
    _ = d33.values a ((Fin.last 29).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d33 _).values a (Fin.castSucc ((Fin.last 29).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d33 _ ((Fin.last 29).castSucc.castSucc.castSucc)
    _ = d32.values a ((Fin.last 29).castSucc.castSucc) := by
      change (Dag.snoc d32 _).values a (Fin.castSucc ((Fin.last 29).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d32 _ ((Fin.last 29).castSucc.castSucc)
    _ = d31.values a ((Fin.last 29).castSucc) := by
      change (Dag.snoc d31 _).values a (Fin.castSucc ((Fin.last 29).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d31 _ ((Fin.last 29).castSucc)
    _ = d30.values a ((Fin.last 29)) := by
      change (Dag.snoc d30 _).values a (Fin.castSucc ((Fin.last 29))) = _
      exact Norm38MacroCuts.snoc_previous a d30 _ ((Fin.last 29))

theorem d36_F_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d36.values a ((Fin.last 31).castSucc.castSucc.castSucc.castSucc) = d32.values a ((Fin.last 31)) := by
  calc
    d36.values a ((Fin.last 31).castSucc.castSucc.castSucc.castSucc) =
        d35.values a ((Fin.last 31).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d35 _).values a (Fin.castSucc ((Fin.last 31).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d35 _ ((Fin.last 31).castSucc.castSucc.castSucc)
    _ = d34.values a ((Fin.last 31).castSucc.castSucc) := by
      change (Dag.snoc d34 _).values a (Fin.castSucc ((Fin.last 31).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d34 _ ((Fin.last 31).castSucc.castSucc)
    _ = d33.values a ((Fin.last 31).castSucc) := by
      change (Dag.snoc d33 _).values a (Fin.castSucc ((Fin.last 31).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d33 _ ((Fin.last 31).castSucc)
    _ = d32.values a ((Fin.last 31)) := by
      change (Dag.snoc d32 _).values a (Fin.castSucc ((Fin.last 31))) = _
      exact Norm38MacroCuts.snoc_previous a d32 _ ((Fin.last 31))

theorem d36_I_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d36.values a ((Fin.last 34).castSucc) = d35.values a ((Fin.last 34)) := by
  calc
    d36.values a ((Fin.last 34).castSucc) =
        d35.values a ((Fin.last 34)) := by
      change (Dag.snoc d35 _).values a (Fin.castSucc ((Fin.last 34))) = _
      exact Norm38MacroCuts.snoc_previous a d35 _ ((Fin.last 34))

theorem prefix_A1 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d37.values a (Fin.last 36) = d36.values a ⟨29, by decide⟩ *
      d36.values a ⟨31, by decide⟩ * d36.values a ⟨34, by decide⟩ := by
  rw [d37, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d36_D_carry
#print axioms d36_F_carry
#print axioms d36_I_carry
#print axioms prefix_A1
end DiophantineConsistency.Norm38MacroDependent07
