import DiophantineConsistency.Norm38MacroDependentE

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent05
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d31_A_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d31.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d24.values a ((Fin.last 23)) := by
  calc
    d31.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d30.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d30 _).values a (Fin.castSucc ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d30 _ ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d29.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d29 _ ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d28.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc) := by
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

theorem prefix_F {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d32.values a (Fin.last 31) = ((d31.values a ⟨23, by decide⟩) ^ (2 : Nat) - ((1 : Int) : R)) *
      (d31.values a ⟨30, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R) := by
  rw [d32, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d31_A_carry
#print axioms prefix_F
end DiophantineConsistency.Norm38MacroDependent05
