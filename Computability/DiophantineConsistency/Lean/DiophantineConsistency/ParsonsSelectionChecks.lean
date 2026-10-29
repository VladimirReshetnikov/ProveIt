import DiophantineConsistency.ParsonsSelection
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsSelectionChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open ParsonsSelection

-- The context can itself contain further copies of the principal conjunction.
example {L : Language} {A B : Proposition L} {Γ : Sequent L}
    (d : Derivation ((A ⋏ B) :: (A ⋏ B) :: Γ)) (h : Derivation.IsCutFree d) :
    ∃ e : Derivation (A :: (A ⋏ B) :: Γ),
      Derivation.IsCutFree e ∧ e.height ≤ d.height := invert_left d h

-- The nonprincipal conjunction can also be selected simultaneously.
example {L : Language} {A B : Proposition L} {Γ : Sequent L}
    (d : Derivation ((A ⋏ B) :: (A ⋏ B) :: Γ)) (h : Derivation.IsCutFree d) :
    ∃ e : Derivation (B :: B :: Γ), Derivation.IsCutFree e ∧ e.height ≤ d.height :=
  invert h (.replace (.replace (same A B B Γ))) (Or.inr rfl)

-- Joosten's three matrix conjuncts each retain the original height bound.
example {L : Language} {A B C : Proposition L} {Γ : Sequent L}
    (d : Derivation ((A ⋏ (B ⋏ C)) :: Γ)) (h : Derivation.IsCutFree d) :
    (∃ e : Derivation (A :: Γ), Derivation.IsCutFree e ∧ e.height ≤ d.height) ∧
    (∃ e : Derivation (B :: Γ), Derivation.IsCutFree e ∧ e.height ≤ d.height) ∧
    (∃ e : Derivation (C :: Γ), Derivation.IsCutFree e ∧ e.height ≤ d.height) :=
  invert_three d h

#print axioms choice
#print axioms pullback
#print axioms shift
#print axioms invert
#print axioms invert_left
#print axioms invert_right
#print axioms invert_three
end DiophantineConsistency.ParsonsSelectionChecks
