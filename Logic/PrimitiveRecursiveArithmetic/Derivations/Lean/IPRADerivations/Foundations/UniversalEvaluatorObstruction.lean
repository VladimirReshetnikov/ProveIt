import IPRADerivations.Core.Evaluation
import IPRADerivations.Foundations.EmbeddingBasics

/-!
# The universal primitive-recursive evaluator obstruction

FIBER Section 2, “No primitive-recursive universal evaluator”, and the
embedding framework's `prop:no-universal-pr-evaluator`.

The object theorem is the universally closed diagonal obstruction for every
fixed binary PR symbol. The external theorem states that no such symbol can
enumerate the standard values of every unary PR symbol. It uses the actual
shared evaluator `PR.ev`, rather than postulating a universal evaluator as an
object-language function or assuming the desired diagonal contradiction.
The external semantic assertion is explicitly distinguished from the ordinary
`Prf PRAAx` sentence.
-/

namespace LeanProofs.IPRA.Foundations.UniversalEvaluatorObstruction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.EmbeddingBasics (diagB no_universal_evaluator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app)

/-- The diagonal program computes the candidate evaluator plus one. -/
theorem diagonal_value (E : PR 2) (x : ℕ) :
    PR.ev (diagB E) ![x] = PR.ev E ![x, x] + 1 := by
  simp [diagB, PR.ev]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- No binary PR program represents all unary PR programs by natural indices.
This is a metatheorem about standard evaluation, as in the source statement. -/
theorem no_universal_primitive_recursive_evaluator (E : PR 2) :
    ¬ (∀ f : PR 1, ∃ e : ℕ, ∀ x : ℕ, PR.ev E ![e, x] = PR.ev f ![x]) := by
  intro enumerates
  obtain ⟨e, agrees⟩ := enumerates (diagB E)
  have contradiction := agrees e
  rw [diagonal_value] at contradiction
  exact Nat.ne_of_lt (Nat.lt_succ_self _) contradiction

/-- The index is internal; the program and its diagonal are fixed symbols. -/
def diagonalFormula (E : PR 2) : Fm PTm 1 :=
  neg (.all (app E ![Syn.shift (var 0), var 0] ≐
    app (diagB E) (fun _ => var 0)))

theorem diagonal_obstruction (E : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (diagonalFormula E) :=
  closeUniv 1 (no_universal_evaluator E (var 0))

#print axioms diagonal_value
#print axioms no_universal_primitive_recursive_evaluator
#print axioms diagonal_obstruction

end LeanProofs.IPRA.Foundations.UniversalEvaluatorObstruction
