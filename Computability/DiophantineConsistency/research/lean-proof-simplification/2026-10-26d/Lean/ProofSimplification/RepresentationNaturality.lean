import DiophantineConsistency.Representation

/-!
Small, additive proof-refactoring prototype for ProveIt commit
60e9c5d620c6c387d932876cfa2d9376f64ea56c. The representation data are
unchanged; only the correctness proofs use a shared naturality lemma.
-/
namespace DiophantineConsistency.ProofRefactor

variable {σ τ α β : Type*}

/-- Input and witness renaming commute with the natural-to-integer assignment. -/
theorem natAssignment_comp_sumMap (v : τ → ℕ) (w : β → ℕ)
    (f : σ → τ) (g : α → β) :
    natAssignment v w ∘ Sum.map f g = natAssignment (v ∘ f) (w ∘ g) := by
  funext i
  cases i <;> rfl

/-- One interface replaces repeated `congrArg`/`funext` proofs at call sites. -/
theorem eval_rename_natAssignment (e : Expr (σ ⊕ α))
    (f : σ → τ) (g : α → β) (v : τ → ℕ) (w : β → ℕ) :
    (e.rename (Sum.map f g)).eval (natAssignment v w) =
      e.eval (natAssignment (v ∘ f) (w ∘ g)) := by
  rw [Expr.eval_rename, natAssignment_comp_sumMap]

variable {P Q : (σ → ℕ) → Prop}

/-- Reindexing needs only the shared naturality equation. -/
def reindex (r : Rep σ P) (f : σ → τ) : Rep τ (fun v => P (v ∘ f)) where
  witnessCount := r.witnessCount
  expression := r.expression.rename (Sum.map f id)
  correct v := by
    simpa only [eval_rename_natAssignment, Function.comp_id] using r.correct (v ∘ f)

/-- The same conjunction data, with all four block/assignment adapters shared. -/
def conjunction (r : Rep σ P) (s : Rep σ Q) : Rep σ (fun v => P v ∧ Q v) := by
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

/-- The same disjunction data; the unused witness block remains all zero. -/
def disjunction (r : Rep σ P) (s : Rep σ Q) : Rep σ (fun v => P v ∨ Q v) := by
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

/-- Data preservation includes both syntax and witness count. -/
theorem reindex_eq (r : Rep σ P) (f : σ → τ) :
    reindex r f = r.reindex f := by rfl

theorem conjunction_eq (r : Rep σ P) (s : Rep σ Q) :
    conjunction r s = r.conjunction s := by rfl

theorem disjunction_eq (r : Rep σ P) (s : Rep σ Q) :
    disjunction r s = r.disjunction s := by rfl

#print axioms natAssignment_comp_sumMap
#print axioms eval_rename_natAssignment
#print axioms reindex
#print axioms conjunction
#print axioms disjunction
#print axioms reindex_eq
#print axioms conjunction_eq
#print axioms disjunction_eq

end DiophantineConsistency.ProofRefactor
