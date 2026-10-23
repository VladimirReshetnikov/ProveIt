import DiophantineConsistency.CompactedJones

open DiophantineConsistency
open WitnessCompaction

private def sparseLeft : NatExpr (Empty ⊕ Fin 10) := .var (Sum.inr 7)
private def sparseRight : NatExpr (Empty ⊕ Fin 10) := .constant 42

/-- Nine of the ten source coordinates are unused. -/
example : count sparseLeft sparseRight = 1 := by decide

/-- The packed coordinate still supplies the intended value. -/
example : (leftClosed sparseLeft sparseRight).eval (Sum.elim Empty.elim (fun _ => 42)) =
    (rightClosed sparseLeft sparseRight).eval (Sum.elim Empty.elim (fun _ => 42)) := by decide

/-- Constant equations require no original witness coordinates. -/
example : count (0 : NatExpr (Empty ⊕ Fin 10)) 0 = 0 := by decide

example : (∃ w : Fin 10 → ℕ,
    sparseLeft.eval (Sum.elim Empty.elim w) = sparseRight.eval (Sum.elim Empty.elim w)) ↔
    ∃ w : Fin (count sparseLeft sparseRight) → ℕ,
      (leftClosed sparseLeft sparseRight).eval (Sum.elim Empty.elim w) =
        (rightClosed sparseLeft sparseRight).eval (Sum.elim Empty.elim w) :=
  exists_closed_eval_eq_iff sparseLeft sparseRight

/-- Packing preserves every listed coordinate even if the source list repeats it. -/
example (v : Fin 3 → ℕ) : unpack [1, 1, 2] (pack [1, 1, 2] v) 1 = v 1 :=
  unpack_pack_of_mem [1, 1, 2] v (by decide)

#print axioms WitnessCompaction.exists_eval_eq_iff
#print axioms CompactedJones.expression_correct
