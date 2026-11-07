import DiophantineConsistency.Sign33MacroDependentK

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroDependent03
open Sign33MacroLanguage Sign33MacroPrefixes

theorem d23_M_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d23.values a ((Fin.last 20).castSucc.castSucc) = d21.values a ((Fin.last 20)) := by
  calc
    d23.values a ((Fin.last 20).castSucc.castSucc) =
        d22.values a ((Fin.last 20).castSucc) := by
      change (Dag.snoc d22 _).values a (Fin.castSucc ((Fin.last 20).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d22 _ ((Fin.last 20).castSucc)
    _ = d21.values a ((Fin.last 20)) := by
      change (Dag.snoc d21 _).values a (Fin.castSucc ((Fin.last 20))) = _
      exact Sign33MacroCuts.snoc_previous a d21 _ ((Fin.last 20))

theorem d23_U_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d23.values a ((Fin.last 18).castSucc.castSucc.castSucc.castSucc) = d19.values a ((Fin.last 18)) := by
  calc
    d23.values a ((Fin.last 18).castSucc.castSucc.castSucc.castSucc) =
        d22.values a ((Fin.last 18).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d22 _).values a (Fin.castSucc ((Fin.last 18).castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d22 _ ((Fin.last 18).castSucc.castSucc.castSucc)
    _ = d21.values a ((Fin.last 18).castSucc.castSucc) := by
      change (Dag.snoc d21 _).values a (Fin.castSucc ((Fin.last 18).castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d21 _ ((Fin.last 18).castSucc.castSucc)
    _ = d20.values a ((Fin.last 18).castSucc) := by
      change (Dag.snoc d20 _).values a (Fin.castSucc ((Fin.last 18).castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d20 _ ((Fin.last 18).castSucc)
    _ = d19.values a ((Fin.last 18)) := by
      change (Dag.snoc d19 _).values a (Fin.castSucc ((Fin.last 18))) = _
      exact Sign33MacroCuts.snoc_previous a d19 _ ((Fin.last 18))

theorem prefix_A {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d24.values a (Fin.last 23) = d23.values a ⟨20, by decide⟩ *
      (d23.values a ⟨18, by decide⟩ + ((1 : Int) : R)) := by
  rw [d24, Sign33MacroCuts.snoc_last]
  rfl

#print axioms d23_M_carry
#print axioms d23_U_carry
#print axioms prefix_A
end DiophantineConsistency.Sign33MacroDependent03
