import DiophantineConsistency.ArithmeticRepresentation
import Mathlib.Data.Fin.VecNotation

/-!
# Existential acceptance from a supplied unary computation graph

The input and output become finite natural witnesses. The output is fixed
to the supplied accepted value; no search is performed when constructing
the expression data.
-/

namespace DiophantineConsistency.GraphRep

/-- Convert supplied graph data into a closed representation of attaining a
specified value. The expression is fixed independently of any witness. -/
def existsValue {f : ℕ → ℕ}
    (r : GraphRep (fun v : Fin 1 → ℕ => f (v 0))) (accepted : ℕ) :
    Rep Empty (fun _ => ∃ t, f t = accepted) := by
  let index : Option (Fin 1) → Empty ⊕ Fin 2
    | none => .inr 0
    | some _ => .inr 1
  let output : Rep (Empty ⊕ Fin 2) (fun v => v (.inr 0) = accepted) :=
    (Rep.equality (Expr.var (.inr (0 : Fin 2))) (Expr.constant accepted)).ofIff
      (fun v => by simp only [Expr.eval, Int.natCast_inj])
  refine (((Rep.reindex r index).conjunction output).existsBlock).ofIff ?_
  intro v
  change (∃ w : Fin 2 → ℕ, w 0 = f (w 1) ∧ w 0 = accepted) ↔ ∃ t, f t = accepted
  constructor
  · rintro ⟨w, hw, ha⟩
    exact ⟨w 1, hw.symm.trans ha⟩
  · rintro ⟨t, ht⟩
    exact ⟨![accepted, t], ht.symm, rfl⟩

end DiophantineConsistency.GraphRep
