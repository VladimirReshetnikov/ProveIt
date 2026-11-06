import DiophantineConsistency.Norm38MacroLive18Group01

/-! Candidate short-prefix U evaluator; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent01
open Norm38MacroLanguage Norm38MacroPrefixes

theorem prefix_U {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d19.values a (Fin.last 18) = (d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) ^ (2 : Nat) *
      d18.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc) := by
  rw [d19, Norm38MacroCuts.snoc_last]
  rfl

#print axioms prefix_U
end DiophantineConsistency.Norm38MacroDependent01
