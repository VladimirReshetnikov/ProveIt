import DiophantineConsistency.ComposeRepresentation
import Mathlib.Data.Fin.VecNotation

/-!
# Explicit data for truncated natural subtraction

The active difference branch and the zero branch are supplied as arithmetic
syntax. General graph substitution retains all witness data.
-/

namespace DiophantineConsistency.GraphRep

/-- A fixed finite representation of the binary natural subtraction graph. -/
def subCoordinates : GraphRep (fun v : Fin 2 → ℕ => v 0 - v 1) := by
  let first := Rep.equality (Expr.var (some (0 : Fin 2)))
    (Expr.var none + Expr.var (some (1 : Fin 2)))
  let second := (ArithmeticRep.le (some (0 : Fin 2)) (some (1 : Fin 2))).conjunction
    (Rep.equality (Expr.var (none : Option (Fin 2))) 0)
  refine (first.disjunction second).ofIff ?_
  intro v
  simp only [Expr.eval, Function.comp_apply]
  omega

/-- Subtraction of two explicitly represented natural-valued functions. -/
def sub {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) : GraphRep (fun v => f v - g v) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))
  exact GraphRep.compose subCoordinates arguments

end DiophantineConsistency.GraphRep
