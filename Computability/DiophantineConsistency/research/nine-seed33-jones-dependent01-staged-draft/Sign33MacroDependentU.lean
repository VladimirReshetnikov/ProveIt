import DiophantineConsistency.Sign33MacroLive18Group01

/-! Candidate short-prefix U evaluator; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroDependent01
open Sign33MacroLanguage Sign33MacroPrefixes

theorem prefix_U {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d19.values a (Fin.last 18) = (d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) ^ (2 : Nat) *
      d18.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc) := by
  rw [d19, Sign33MacroCuts.snoc_last]
  rfl

#print axioms prefix_U
end DiophantineConsistency.Sign33MacroDependent01
