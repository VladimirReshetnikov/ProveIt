import DiophantineConsistency.ComposeRepresentation
import Mathlib.Data.Fin.VecNotation

/-!
# Explicit graph data for natural-valued conditional branches

Equality and its complementary pair of strict inequalities select one of two
supplied values. Both branch graphs are ordinary finite polynomial data; no
classifier is extracted from a proposition-valued computability proof.
-/

namespace DiophantineConsistency.GraphRep

private def equalityAt {σ : Type*} (i j : σ) : Rep σ (fun v => v i = v j) :=
  (Rep.equality (.var i) (.var j)).ofIff (fun v => by
    simp only [Expr.eval, Int.natCast_inj])

/-- The graph of an equality branch on four explicit input coordinates. -/
def ifEqCoordinates : GraphRep (fun v : Fin 4 → ℕ =>
    if v 0 = v 1 then v 2 else v 3) := by
  let equal := equalityAt (some (0 : Fin 4)) (some 1)
  let unequal := (ArithmeticRep.lt (some (0 : Fin 4)) (some 1)).disjunction
    (ArithmeticRep.lt (some (1 : Fin 4)) (some 0))
  let thenValue := equalityAt (none : Option (Fin 4)) (some 2)
  let elseValue := equalityAt (none : Option (Fin 4)) (some 3)
  refine ((equal.conjunction thenValue).disjunction
    (unequal.conjunction elseValue)).ofIff ?_
  intro v
  change ((v (some 0) = v (some 1) ∧ v none = v (some 2)) ∨
    ((v (some 0) < v (some 1) ∨ v (some 1) < v (some 0)) ∧ v none = v (some 3))) ↔
      v none = if v (some 0) = v (some 1) then v (some 2) else v (some 3)
  by_cases h : v (some 0) = v (some 1)
  · simp [h]
  · have hlt := lt_or_gt_of_ne h
    simp [h, hlt]

/-- Equality branching on explicitly represented functions. -/
def ifEq {σ : Type*} {f g h k : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) (t : GraphRep h) (u : GraphRep k) :
    GraphRep (fun v => if f v = g v then h v else k v) := by
  let arguments : ∀ i : Fin 4, GraphRep (![f, g, h, k] i) :=
    Fin.cases r (Fin.cases s (Fin.cases t (Fin.cases u (fun i => Fin.elim0 i))))
  exact GraphRep.compose ifEqCoordinates arguments

/-- Zero branching is equality branching with the supplied constant zero. -/
def ifZero {σ : Type*} {f g h : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) (t : GraphRep h) :
    GraphRep (fun v => if f v = 0 then g v else h v) :=
  ifEq r (GraphRep.constant 0) s t

end DiophantineConsistency.GraphRep
