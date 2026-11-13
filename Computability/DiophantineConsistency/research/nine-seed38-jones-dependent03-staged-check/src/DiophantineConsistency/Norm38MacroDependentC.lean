import DiophantineConsistency.Norm38MacroDependentW

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent03
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d26_phi_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d26.values a ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d18.values a ((Fin.last 14).castSucc.castSucc.castSucc) := by
  calc
    d26.values a ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) =
        d25.values a ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d25 _).values a (Fin.castSucc ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d25 _ ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d24.values a ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d24 _).values a (Fin.castSucc ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d24 _ ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d23.values a ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d23 _).values a (Fin.castSucc ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d23 _ ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d22.values a ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d22 _).values a (Fin.castSucc ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d22 _ ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d21.values a ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d21 _).values a (Fin.castSucc ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d21 _ ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d20.values a ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d20 _).values a (Fin.castSucc ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d20 _ ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d19.values a ((Fin.last 14).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d19 _).values a (Fin.castSucc ((Fin.last 14).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d19 _ ((Fin.last 14).castSucc.castSucc.castSucc.castSucc)
    _ = d18.values a ((Fin.last 14).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d18 _).values a (Fin.castSucc ((Fin.last 14).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d18 _ ((Fin.last 14).castSucc.castSucc.castSucc)

theorem prefix_C {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d27.values a (Fin.last 26) = d26.values a ⟨24, by decide⟩ +
      d26.values a ⟨25, by decide⟩ + d26.values a ⟨14, by decide⟩ := by
  rw [d27, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d26_phi_carry
#print axioms prefix_C
end DiophantineConsistency.Norm38MacroDependent03
