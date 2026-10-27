import DiophantineConsistency.FoundationPAHFOrdinarySemantics

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationPAHFOrdinarySemanticsChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open SetTheory.PA HA FoundationPAHFSyntax FoundationHADeltaZero
open FoundationPAHFNatSemantics FoundationPAHFOrdinarySemantics

example (s t : Term) (k : Nat) :
    Formula.Free k (ltFormula s t) ↔ Term.Free k s ∨ Term.Free k t :=
  free_ltFormula s t k

-- The order witness does not become an outside free variable.
example : Formula.Sentence (ltFormula .zero (.succ .zero)) := by
  intro k hk
  exact ((free_ltFormula _ _ _).mp hk).elim False.elim False.elim

-- Nested binders shift only the ambient sparse parameter, not slot one.
example (fv : Nat → Term) :
    ordinaryAux Fin.elim0 fv
      (.all (.exs (.nrel .lt ![.bvar 1, .fvar 7]))) =
    .all (.ex (neg (ltFormula (.var 1)
      (Term.rename Nat.succ (Term.rename Nat.succ (fv 7)))))) := rfl

example (fv : Nat → Term) (p : Semiformula ℒₒᵣ Nat 0) (k : Nat)
    (h : Formula.Free k (ordinaryAux Fin.elim0 (liftFree fv) p)) :
    ∃ x, Term.Free k (liftFree fv x) := by
  rcases free_ordinaryAux Fin.elim0 (liftFree fv) p k h with ⟨i,_⟩ | hx
  · exact Fin.elim0 i
  · exact hx

example (p : Semiformula ℒₒᵣ Empty 2) :
    Formula.Sentence (ordinaryAux Fin.elim0 Empty.elim (.all (.exs p))) :=
  ordinary_sentence _

example {α : Type*} (M : PreModel α) (p : ArithmeticSentence) (ee ff : Nat → α) :
    Formula.Sat M ee (ordinaryAux Fin.elim0 Empty.elim p) ↔
      Formula.Sat M ff (ordinaryAux Fin.elim0 Empty.elim p) :=
  ordinary_sentence_environment M p ee ff

example (fv : Nat → Term) (ee : Nat → Nat) :
    Formula.Sat natStructure ee (ordinaryAux Fin.elim0 fv
      (.nrel .eq ![.fvar 0, .fvar 9])) ↔
      Term.eval natStructure ee (fv 0) ≠ Term.eval natStructure ee (fv 9) :=
  sat_ordinaryAux _ _ _ _

example (p : ArithmeticSentence) (ee : Nat → Nat) :
    Formula.Sat natStructure ee (ordinaryAux Fin.elim0 Empty.elim p) ↔
      p.Evalb (M := Nat) ![] := sat_ordinary_sentence p ee

#print axioms free_rename_succ
#print axioms free_termAux
#print axioms free_ltFormula
#print axioms free_ordinaryAux
#print axioms ordinary_sentence
#print axioms ordinary_sentence_environment
#print axioms sat_ordinaryAux
#print axioms sat_ordinary_sentence
end DiophantineConsistency.FoundationPAHFOrdinarySemanticsChecks
