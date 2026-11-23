import ConciseIPRA.PR

/-!
# Actual ProveIt object-logic proof candidates

These constructor expressions target `Prf PRAAx`, not merely ambient Lean
truth. Their interface was checked against ProveIt commit
803d951d15834da5571e26d1f39988d921b29760. They have NOT been compiled here,
because no Lean toolchain was available. They do not constitute the numerical
arithmetization of the decision algorithms in the accompanying report.
-/

namespace LeanProofs.ConciseIPRA.PropositionalExamples

open scoped Fm

variable {n : Nat} (a b c : Fm PTm n)

/-- Identity is a derivation schema in the object theory. -/
theorem identity : Prf PRAAx [] (a ⟶ a) :=
  .impI Prf.hyp0

theorem conjunction_commutes : Prf PRAAx [] ((a ⋏ b) ⟶ (b ⋏ a)) :=
  .impI (.andI (.andE₂ Prf.hyp0) (.andE₁ Prf.hyp0))

theorem disjunction_commutes : Prf PRAAx [] ((a ⋎ b) ⟶ (b ⋎ a)) :=
  .impI (.orE Prf.hyp0 (.orI₂ Prf.hyp0) (.orI₁ Prf.hyp0))

theorem composition :
    Prf PRAAx [] (((a ⟶ b) ⋏ (b ⟶ c)) ⟶ (a ⟶ c)) :=
  .impI (.impI (.impE (.andE₂ Prf.hyp1)
    (.impE (.andE₁ Prf.hyp1) Prf.hyp0)))

theorem double_negation_intro :
    Prf PRAAx [] (a ⟶ ((a ⟶ Fm.bot) ⟶ Fm.bot)) :=
  .impI (.impI (.impE Prf.hyp0 Prf.hyp1))

theorem double_negation_excluded_middle :
    Prf PRAAx [] (((a ⋎ (a ⟶ Fm.bot)) ⟶ Fm.bot) ⟶ Fm.bot) :=
  .impI (.impE Prf.hyp0
    (.orI₂ (.impI (.impE Prf.hyp1 (.orI₁ Prf.hyp0)))))

theorem explosion : Prf PRAAx [] (Fm.bot ⟶ a) :=
  .impI (.botE a Prf.hyp0)

/-- Unary and binary PR applications, with no universal PR evaluator. -/
def applyOne {k : Nat} (f : PR 1) (x : PTm k) : PTm k :=
  PTm.app f (fun _ => x)

def applyTwo {k : Nat} (f : PR 2) (x y : PTm k) : PTm k :=
  PTm.app f (Fin.cases x (fun _ => y))

/-- Exact closed endpoint for classical numerical completeness.
`check` is the two-argument checker for an empty-context CPC proof of `a`.
The four PR symbols must be implemented and their specifications proved;
this definition does not assert the resulting sentence is derivable. -/
def classicalCompletenessSentence
    (valid taut prove : PR 1) (check : PR 2) : Fm PTm 0 :=
  let x : PTm 1 := PTm.var 0
  let one : PTm 1 := PTm.succ PTm.zero
  Fm.all (((applyOne valid x ≐ one) ⋏ (applyOne taut x ≐ one)) ⟶
    (applyTwo check (applyOne prove x) x ≐ one))

/-- Exact closed endpoint for an IPC proof-or-countermodel construction.
`countercheck(m,a)` checks a nonempty rooted finite model refuting `a`.
The functions are fixed PR symbols, not arbitrary programs being evaluated. -/
def ipcCompletenessSentence
    (valid prove model : PR 1) (check countercheck : PR 2) : Fm PTm 0 :=
  let x : PTm 1 := PTm.var 0
  let one : PTm 1 := PTm.succ PTm.zero
  Fm.all ((applyOne valid x ≐ one) ⟶
    ((applyTwo check (applyOne prove x) x ≐ one) ⋎
     (applyTwo countercheck (applyOne model x) x ≐ one)))

/-- A closed quantified arithmetic example of the endpoint discipline. -/
theorem unary_predicate_identity (f : PR 1) :
    Prf PRAAx [] (Fm.all
      ((applyOne f (PTm.var 0 : PTm 1) ≐ PTm.succ PTm.zero) ⟶
       (applyOne f (PTm.var 0 : PTm 1) ≐ PTm.succ PTm.zero))) :=
  .allI (.impI Prf.hyp0)

end LeanProofs.ConciseIPRA.PropositionalExamples
