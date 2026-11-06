import DiophantineConsistency.Norm38MacroDependentA1

/-! Candidate dependent prefix evaluation and live carry; no full-recipe theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroDependent07
open Norm38MacroLanguage Norm38MacroPrefixes

theorem d37_A0_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d37.values a ((Fin.last 35).castSucc) = d36.values a ((Fin.last 35)) := by
  calc
    d37.values a ((Fin.last 35).castSucc) =
        d36.values a ((Fin.last 35)) := by
      change (Dag.snoc d36 _).values a (Fin.castSucc ((Fin.last 35))) = _
      exact Norm38MacroCuts.snoc_previous a d36 _ ((Fin.last 35))

theorem d38_A1_carry {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d38.values a ((Fin.last 36).castSucc) = d37.values a ((Fin.last 36)) := by
  calc
    d38.values a ((Fin.last 36).castSucc) =
        d37.values a ((Fin.last 36)) := by
      change (Dag.snoc d37 _).values a (Fin.castSucc ((Fin.last 36))) = _
      exact Norm38MacroCuts.snoc_previous a d37 _ ((Fin.last 36))

theorem prefix_V0 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d38.values a (Fin.last 37) = (d37.values a ⟨35, by decide⟩) ^ (2 : Nat) + ((2 : Int) : R) := by
  rw [d38, Norm38MacroCuts.snoc_last]
  rfl

theorem prefix_V1 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d39.values a (Fin.last 38) = (d38.values a ⟨36, by decide⟩) ^ (2 : Nat) + ((2 : Int) : R) := by
  rw [d39, Norm38MacroCuts.snoc_last]
  rfl

#print axioms d37_A0_carry
#print axioms d38_A1_carry
#print axioms prefix_V0
#print axioms prefix_V1
end DiophantineConsistency.Norm38MacroDependent07
