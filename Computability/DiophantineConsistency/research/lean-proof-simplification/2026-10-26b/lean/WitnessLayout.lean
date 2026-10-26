import DiophantineConsistency.Representation

/-!
Prototype for a small, data-preserving witness-layout API.
The original repository files are not modified.  These definitions use the
same witness counts and expressions as Rep.conjunction and Rep.disjunction.
-/
namespace DiophantineConsistency.ProofSimplification

variable {σ τ ι κ : Type*}

@[simp] theorem natAssignment_comp_sumMap
    (v : τ → ℕ) (w : κ → ℕ) (f : σ → τ) (g : ι → κ) :
    natAssignment v w ∘ Sum.map f g = natAssignment (v ∘ f) (w ∘ g) := by
  funext i
  cases i <;> rfl

theorem eval_rename_natAssignment (e : Expr (σ ⊕ ι))
    (v : τ → ℕ) (w : κ → ℕ) (f : σ → τ) (g : ι → κ) :
    (e.rename (Sum.map f g)).eval (natAssignment v w) =
      e.eval (natAssignment (v ∘ f) (w ∘ g)) := by
  rw [Expr.eval_rename, natAssignment_comp_sumMap]

/-- Move between a single concatenated witness block and its two components. -/
theorem exists_split_witnesses {m n : ℕ}
    (P : (Fin m → ℕ) → (Fin n → ℕ) → Prop) :
    (∃ w : Fin (m + n) → ℕ,
      P (w ∘ Fin.castAdd n) (w ∘ Fin.natAdd m)) ↔
        ∃ a b, P a b := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w ∘ Fin.castAdd n, w ∘ Fin.natAdd m, hw⟩
  · rintro ⟨a, b, h⟩
    refine ⟨Fin.addCases a b, ?_⟩
    simpa [Function.comp_def] using h

variable {P Q : (σ → ℕ) → Prop}

/-- Same data as Rep.conjunction, with common layout reasoning factored out. -/
def conjunctionCompact (r : Rep σ P) (s : Rep σ Q) : Rep σ (fun v => P v ∧ Q v) := by
  let left := r.expression.rename (Sum.map id (Fin.castAdd s.witnessCount))
  let right := s.expression.rename (Sum.map id (Fin.natAdd r.witnessCount))
  refine ⟨r.witnessCount + s.witnessCount, left * left + right * right, ?_⟩
  intro v
  simp only [left, right, Expr.eval_add, Expr.eval_mul,
    eval_rename_natAssignment, Function.comp_id, mul_self_add_mul_self_eq_zero]
  rw [exists_split_witnesses (m := r.witnessCount) (n := s.witnessCount)
    (fun a b => r.expression.eval (natAssignment v a) = 0 ∧
      s.expression.eval (natAssignment v b) = 0), r.correct, s.correct]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a, b, ha, hb⟩
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩

/-- Same data as Rep.disjunction; the unused witness block is filled by zero. -/
def disjunctionCompact (r : Rep σ P) (s : Rep σ Q) : Rep σ (fun v => P v ∨ Q v) := by
  let left := r.expression.rename (Sum.map id (Fin.castAdd s.witnessCount))
  let right := s.expression.rename (Sum.map id (Fin.natAdd r.witnessCount))
  refine ⟨r.witnessCount + s.witnessCount, left * right, ?_⟩
  intro v
  simp only [left, right, Expr.eval_mul, eval_rename_natAssignment,
    Function.comp_id, mul_eq_zero]
  rw [exists_split_witnesses (m := r.witnessCount) (n := s.witnessCount)
    (fun a b => r.expression.eval (natAssignment v a) = 0 ∨
      s.expression.eval (natAssignment v b) = 0), r.correct, s.correct]
  constructor
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · exact ⟨a, fun _ => 0, Or.inl ha⟩
    · exact ⟨fun _ => 0, b, Or.inr hb⟩
  · rintro ⟨a, b, ha | hb⟩
    · exact Or.inl ⟨a, ha⟩
    · exact Or.inr ⟨b, hb⟩

-- The executable data are definitionally unchanged.
example (r : Rep σ P) (s : Rep σ Q) :
    (conjunctionCompact r s).witnessCount = (r.conjunction s).witnessCount := rfl

example (r : Rep σ P) (s : Rep σ Q) :
    (disjunctionCompact r s).witnessCount = (r.disjunction s).witnessCount := rfl

example (r : Rep σ P) (s : Rep σ Q) :
    (conjunctionCompact r s).expression = (r.conjunction s).expression := rfl

example (r : Rep σ P) (s : Rep σ Q) :
    (disjunctionCompact r s).expression = (r.disjunction s).expression := rfl

#print axioms natAssignment_comp_sumMap
#print axioms eval_rename_natAssignment
#print axioms exists_split_witnesses
#print axioms conjunctionCompact
#print axioms disjunctionCompact
end DiophantineConsistency.ProofSimplification
