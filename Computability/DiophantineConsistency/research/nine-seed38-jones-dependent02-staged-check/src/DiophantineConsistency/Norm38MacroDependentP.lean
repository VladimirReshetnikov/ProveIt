import DiophantineConsistency.Norm38MacroDependentM

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent02
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d21_U_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d21.values a ((Fin.last 18).castSucc.castSucc) = d19.values a ((Fin.last 18)) := by
  calc
    d21.values a ((Fin.last 18).castSucc.castSucc) =
        d20.values a ((Fin.last 18).castSucc) := by
      change (Dag.snoc d20 _).values a (Fin.castSucc ((Fin.last 18).castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d20 _ ((Fin.last 18).castSucc)
    _ = d19.values a ((Fin.last 18)) := by
      change (Dag.snoc d19 _).values a (Fin.castSucc ((Fin.last 18))) = _
      exact Norm38MacroCuts.snoc_previous a d19 _ ((Fin.last 18))

theorem prefix_P {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d22.values a (Fin.last 21) = ((2 : Int) : R) *
      (d21.values a ⟨20, by decide⟩) ^ (2 : Nat) * d21.values a ⟨18, by decide⟩ := by
  rw [d22, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d21_U_carry
#print axioms prefix_P
end DiophantineConsistency.Norm38MacroDependent02
