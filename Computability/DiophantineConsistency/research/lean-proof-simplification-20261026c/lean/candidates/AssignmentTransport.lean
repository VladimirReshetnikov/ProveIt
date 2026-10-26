import DiophantineConsistency.Representation

/-!
Small proposed API addition for the pinned ProveIt snapshot.
This file leaves every existing representation's data and statement unchanged.
Verification status is recorded separately by the reproduction driver.
-/

namespace DiophantineConsistency.ProofRefactoring

variable {σ τ α β : Type*}

theorem natAssignment_comp_sumMap (v : τ → ℕ) (w : β → ℕ)
    (f : σ → τ) (g : α → β) :
    natAssignment v w ∘ Sum.map f g =
      natAssignment (v ∘ f) (w ∘ g) := by
  funext i
  cases i <;> rfl

theorem eval_rename_natAssignment (e : Expr (σ ⊕ α))
    (f : σ → τ) (g : α → β) (v : τ → ℕ) (w : β → ℕ) :
    (e.rename (Sum.map f g)).eval (natAssignment v w) =
      e.eval (natAssignment (v ∘ f) (w ∘ g)) := by
  rw [Expr.eval_rename, natAssignment_comp_sumMap]

/-- The left-witness helper repeated in Rep.conjunction and Rep.disjunction. -/
theorem eval_left_block {P : (σ → ℕ) → Prop} (r : Rep σ P)
    (k : ℕ) (v : σ → ℕ) (w : Fin (r.witnessCount + k) → ℕ) :
    (r.expression.rename (Sum.map id (Fin.castAdd k))).eval (natAssignment v w) =
      r.expression.eval (natAssignment v (w ∘ Fin.castAdd k)) := by
  simpa only [Function.comp_id] using
    eval_rename_natAssignment r.expression id (Fin.castAdd k) v w

/-- The right-witness helper repeated in Rep.conjunction and Rep.disjunction. -/
theorem eval_right_block {P : (σ → ℕ) → Prop} (r : Rep σ P)
    (k : ℕ) (v : σ → ℕ) (w : Fin (k + r.witnessCount) → ℕ) :
    (r.expression.rename (Sum.map id (Fin.natAdd k))).eval (natAssignment v w) =
      r.expression.eval (natAssignment v (w ∘ Fin.natAdd k)) := by
  simpa only [Function.comp_id] using
    eval_rename_natAssignment r.expression id (Fin.natAdd k) v w

#print axioms eval_rename_natAssignment
#print axioms eval_left_block
#print axioms eval_right_block

end DiophantineConsistency.ProofRefactoring
