import DiophantineConsistency.Representation

/-! Candidate refactorings, kept separate from the original repository.
The theorems in this file state the same evaluator facts already proved
locally inside representation constructors. -/

namespace DiophantineConsistency.ProofRefactor

variable {σ τ α β : Type*}

theorem natAssignment_map (v : τ → ℕ) (w : β → ℕ)
    (f : σ → τ) (g : α → β) :
    natAssignment v w ∘ Sum.map f g =
      natAssignment (v ∘ f) (w ∘ g) := by
  funext i
  cases i <;> rfl

theorem eval_rename_natAssignment (e : Expr (σ ⊕ α))
    (f : σ → τ) (g : α → β) (v : τ → ℕ) (w : β → ℕ) :
    (e.rename (Sum.map f g)).eval (natAssignment v w) =
      e.eval (natAssignment (v ∘ f) (w ∘ g)) := by
  rw [Expr.eval_rename, natAssignment_map]

def reindex {P : (σ → ℕ) → Prop} (r : Rep σ P) (f : σ → τ) :
    Rep τ (fun v => P (v ∘ f)) where
  witnessCount := r.witnessCount
  expression := r.expression.rename (Sum.map f id)
  correct v := by
    simpa only [eval_rename_natAssignment, Function.comp_id] using r.correct (v ∘ f)

/-- No data fields change relative to the original constructor. -/
theorem reindex_same_expression {P : (σ → ℕ) → Prop}
    (r : Rep σ P) (f : σ → τ) :
    (reindex r f).expression = (Rep.reindex r f).expression := rfl

def conjunction {P Q : (σ → ℕ) → Prop}
    (r : Rep σ P) (s : Rep σ Q) : Rep σ (fun v => P v ∧ Q v) := by
  let left := r.expression.rename (Sum.map id (Fin.castAdd s.witnessCount))
  let right := s.expression.rename (Sum.map id (Fin.natAdd r.witnessCount))
  refine ⟨r.witnessCount + s.witnessCount, left * left + right * right, ?_⟩
  intro v
  simp only [left, right, Expr.eval_add, Expr.eval_mul, eval_rename_natAssignment,
    Function.comp_id, mul_self_add_mul_self_eq_zero]
  rw [r.correct, s.correct]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨Fin.addCases a b, ?_, ?_⟩
    · simpa [Function.comp_def] using ha
    · simpa [Function.comp_def] using hb
  · rintro ⟨w, ha, hb⟩
    exact ⟨⟨w ∘ Fin.castAdd s.witnessCount, ha⟩,
      ⟨w ∘ Fin.natAdd r.witnessCount, hb⟩⟩

def disjunction {P Q : (σ → ℕ) → Prop}
    (r : Rep σ P) (s : Rep σ Q) : Rep σ (fun v => P v ∨ Q v) := by
  let left := r.expression.rename (Sum.map id (Fin.castAdd s.witnessCount))
  let right := s.expression.rename (Sum.map id (Fin.natAdd r.witnessCount))
  refine ⟨r.witnessCount + s.witnessCount, left * right, ?_⟩
  intro v
  simp only [left, right, Expr.eval_mul, eval_rename_natAssignment,
    Function.comp_id, mul_eq_zero]
  rw [r.correct, s.correct]
  constructor
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · refine ⟨Fin.addCases a (fun _ => 0), Or.inl ?_⟩
      simpa [Function.comp_def] using ha
    · refine ⟨Fin.addCases (fun _ => 0) b, Or.inr ?_⟩
      simpa [Function.comp_def] using hb
  · rintro ⟨w, ha | hb⟩
    · exact Or.inl ⟨w ∘ Fin.castAdd s.witnessCount, ha⟩
    · exact Or.inr ⟨w ∘ Fin.natAdd r.witnessCount, hb⟩

theorem conjunction_same_expression {P Q : (σ → ℕ) → Prop}
    (r : Rep σ P) (s : Rep σ Q) :
    (conjunction r s).expression = (Rep.conjunction r s).expression := rfl

theorem disjunction_same_expression {P Q : (σ → ℕ) → Prop}
    (r : Rep σ P) (s : Rep σ Q) :
    (disjunction r s).expression = (Rep.disjunction r s).expression := rfl

#print axioms eval_rename_natAssignment
#print axioms reindex
#print axioms conjunction
#print axioms disjunction

end DiophantineConsistency.ProofRefactor
