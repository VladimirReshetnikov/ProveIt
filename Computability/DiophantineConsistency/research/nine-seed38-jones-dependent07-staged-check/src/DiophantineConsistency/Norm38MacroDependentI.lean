import DiophantineConsistency.Norm38MacroDependentH

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent07
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d34_Gprime_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d34.values a ((Fin.last 32).castSucc) = d33.values a ((Fin.last 32)) := by
  calc
    d34.values a ((Fin.last 32).castSucc) =
        d33.values a ((Fin.last 32)) := by
      change (Dag.snoc d33 _).values a (Fin.castSucc ((Fin.last 32))) = _
      exact Norm38MacroCuts.snoc_previous a d33 _ ((Fin.last 32))

theorem prefix_I {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d35.values a (Fin.last 34) = ((d34.values a ⟨32, by decide⟩) ^ (2 : Nat) - ((1 : Int) : R)) *
      (d34.values a ⟨33, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R) := by
  rw [d35, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d34_Gprime_carry
#print axioms prefix_I
end DiophantineConsistency.Norm38MacroDependent07
