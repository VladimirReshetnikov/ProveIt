import DiophantineConsistency.FoundationPAHFSyntax

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationPAHFSyntaxChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open DiophantineConsistency.FoundationPAHFSyntax

private def pair {α : Type*} (a b : α) : Fin 2 → α := ![a,b]

/-- Bound and free variables remain separate even when their source names agree. -/
example : term (.func .mul (pair (.bvar (0 : Fin 2)) (.fvar 0))) =
    SetTheory.PA.Term.mul (.var 0) (.var 2) := rfl

example : term (.func .add (pair (.func .zero Fin.elim0)
    (.func .one Fin.elim0)) : SyntacticTerm ℒₒᵣ) =
    SetTheory.PA.Term.add .zero (.succ .zero) := rfl

/-- Two source binders plus the order witness: free index zero becomes index three. -/
def nested : Semiformulaᵢ ℒₒᵣ ℕ 0 :=
  .all (.exs (.rel .lt (pair (.bvar 1)
    (.func .add (pair (.bvar 0) (.fvar 0))))))

theorem nested_exact : formula nested =
    SetTheory.PA.Formula.all (.ex (.ex (.eq
      (.add (.var 2) (.succ (.var 0))) (.add (.var 1) (.var 3))))) := rfl

/-- The translated order witness cannot capture either outer binder or free variable. -/
theorem nested_shift_exact : formula (Rewriting.shift nested) =
    SetTheory.PA.Formula.all (.ex (.ex (.eq
      (.add (.var 2) (.succ (.var 0))) (.add (.var 1) (.var 4))))) := rfl

private def instBody : Semiformulaᵢ ℒₒᵣ ℕ 1 :=
  .all (.rel .lt (pair (.bvar 1) (.func .add (pair (.bvar 0) (.fvar 0)))))

private def replacement : SyntacticTerm ℒₒᵣ :=
  .func .add (pair (.fvar 0) (.func .one Fin.elim0))

theorem nested_inst_exact : formula (instBody ⇜ (fun _ => replacement)) =
    SetTheory.PA.Formula.all (.ex (.eq
      (.add (.add (.var 2) (.succ .zero)) (.succ (.var 0)))
      (.add (.var 1) (.var 2)))) := rfl

example : formula (instBody ⇜ (fun _ => replacement)) =
    SetTheory.PA.Formula.subst (SetTheory.PA.Formula.instTerm (term replacement))
      (formula instBody) := formula_inst instBody replacement

example : formula (Rewriting.free instBody) = formula instBody := formula_free instBody

example (φ : Semiformulaᵢ ℒₒᵣ ℕ 0) :
    formula (φ ⇜ (Fin.elim0 : Fin 0 → SyntacticSemiterm ℒₒᵣ 1)) =
      SetTheory.PA.Formula.rename Nat.succ (formula φ) := formula_empty_subst φ

/-- Negation is preserved literally; no negative-translation or stability oracle appears. -/
example (φ : Semiformulaᵢ ℒₒᵣ ℕ 0) :
    formula (.imp φ .falsum) = .imp (formula φ) .bot := rfl

/-- Formula equality is translated with its two ordered arguments. -/
example : formula (.rel .eq (pair (.fvar 2) (.fvar 0)) : Semiformulaᵢ ℒₒᵣ ℕ 0) =
    SetTheory.PA.Formula.eq (.var 2) (.var 0) := rfl

/-- A genuine closed source sentence translates to this closed target sentence. -/
def closedExample : Sentenceᵢ ℒₒᵣ := .all (.rel .eq (pair (.bvar 0) (.bvar 0)))

example : sentence closedExample = SetTheory.PA.Formula.all (.eq (.var 0) (.var 0)) := rfl
example : SetTheory.PA.Formula.Sentence (sentence closedExample) := by
  intro n h
  change n+1 = 0 ∨ n+1 = 0 at h
  omega

#print axioms termAux_subst
#print axioms termAux_rew
#print axioms subst_ltFormula
#print axioms formulaAux_subst
#print axioms formulaAux_rew
#print axioms formulaAux_rename
#print axioms formula_all
#print axioms formula_exs
#print axioms formula_free
#print axioms formula_shift
#print axioms formula_inst
#print axioms formula_empty_subst
#print axioms nested_exact
#print axioms nested_shift_exact
#print axioms nested_inst_exact
end DiophantineConsistency.FoundationPAHFSyntaxChecks
