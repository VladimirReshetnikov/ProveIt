import DiophantineConsistency.Norm38MacroDependentJcarry

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent06
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d32_A_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d32.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d24.values a ((Fin.last 23)) := by
  calc
    d32.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d31.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d31 _).values a (Fin.castSucc ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d31 _ ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d30.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
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

theorem d32_C_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d32.values a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc) = d27.values a ((Fin.last 26)) := by
  calc
    d32.values a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc) =
        d31.values a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d31 _).values a (Fin.castSucc ((Fin.last 26).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d31 _ ((Fin.last 26).castSucc.castSucc.castSucc.castSucc)
    _ = d30.values a ((Fin.last 26).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d30 _).values a (Fin.castSucc ((Fin.last 26).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d30 _ ((Fin.last 26).castSucc.castSucc.castSucc)
    _ = d29.values a ((Fin.last 26).castSucc.castSucc) := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ((Fin.last 26).castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d29 _ ((Fin.last 26).castSucc.castSucc)
    _ = d28.values a ((Fin.last 26).castSucc) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 26).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d28 _ ((Fin.last 26).castSucc)
    _ = d27.values a ((Fin.last 26)) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 26))) = _
      exact Norm38MacroCuts.snoc_previous a d27 _ ((Fin.last 26))

theorem d32_D_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d32.values a ((Fin.last 29).castSucc.castSucc) = d30.values a ((Fin.last 29)) := by
  calc
    d32.values a ((Fin.last 29).castSucc.castSucc) =
        d31.values a ((Fin.last 29).castSucc) := by
      change (Dag.snoc d31 _).values a (Fin.castSucc ((Fin.last 29).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d31 _ ((Fin.last 29).castSucc)
    _ = d30.values a ((Fin.last 29)) := by
      change (Dag.snoc d30 _).values a (Fin.castSucc ((Fin.last 29))) = _
      exact Norm38MacroCuts.snoc_previous a d30 _ ((Fin.last 29))

theorem prefix_Gprime {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d33.values a (Fin.last 32) = d32.values a ⟨23, by decide⟩ +
      d32.values a ⟨31, by decide⟩ * (d32.values a ⟨26, by decide⟩ *
        d32.values a ⟨29, by decide⟩ + ((1 : Int) : R) - d32.values a ⟨23, by decide⟩) := by
  rw [d33, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d32_A_carry
#print axioms d32_C_carry
#print axioms d32_D_carry
#print axioms prefix_Gprime
end DiophantineConsistency.Norm38MacroDependent06
