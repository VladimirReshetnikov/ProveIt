import DiophantineConsistency.Representation

/-!
# Shared assignment transport and unchanged representation data

The representation definitions below have exactly the same witness counts and
expression trees as the pinned repository constructors. Only their correctness
proofs use the shared transport and witness-splitting lemmas.
-/

namespace RefactorPrototype

open DiophantineConsistency

/-- Assignment transport for arbitrary input and witness renamings. -/
theorem assignment_comp {σ τ ι κ : Type*}
    (v : τ → ℕ) (w : κ → ℕ) (f : σ → τ) (g : ι → κ) :
    natAssignment v w ∘ Sum.map f g = natAssignment (v ∘ f) (w ∘ g) := by
  funext i
  cases i <;> rfl

theorem exists_fin_add_and {m n : ℕ}
    (P : (Fin m → ℕ) → Prop) (Q : (Fin n → ℕ) → Prop) :
    (∃ w : Fin (m + n) → ℕ,
      P (w ∘ Fin.castAdd n) ∧ Q (w ∘ Fin.natAdd m)) ↔
        (∃ a, P a) ∧ (∃ b, Q b) := by
  constructor
  · rintro ⟨w, hp, hq⟩
    exact ⟨⟨w ∘ Fin.castAdd n, hp⟩, ⟨w ∘ Fin.natAdd m, hq⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨Fin.addCases a b, by simpa [Function.comp_def] using ha,
      by simpa [Function.comp_def] using hb⟩

/-- The unused witness block is filled with zero. -/
theorem exists_fin_add_or {m n : ℕ}
    (P : (Fin m → ℕ) → Prop) (Q : (Fin n → ℕ) → Prop) :
    (∃ w : Fin (m + n) → ℕ,
      P (w ∘ Fin.castAdd n) ∨ Q (w ∘ Fin.natAdd m)) ↔
        (∃ a, P a) ∨ (∃ b, Q b) := by
  constructor
  · rintro ⟨w, hp | hq⟩
    · exact Or.inl ⟨w ∘ Fin.castAdd n, hp⟩
    · exact Or.inr ⟨w ∘ Fin.natAdd m, hq⟩
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · exact ⟨Fin.addCases a (fun _ => 0), Or.inl (by simpa [Function.comp_def] using ha)⟩
    · exact ⟨Fin.addCases (fun _ => 0) b, Or.inr (by simpa [Function.comp_def] using hb)⟩

variable {σ : Type*} {P Q : (σ → ℕ) → Prop}

def reindexShort {τ : Type*} (r : Rep σ P) (f : σ → τ) :
    Rep τ (fun v => P (v ∘ f)) where
  witnessCount := r.witnessCount
  expression := r.expression.rename (Sum.map f id)
  correct v := by
    simpa only [Expr.eval_rename, assignment_comp, Function.comp_id] using r.correct (v ∘ f)

def conjunctionShort (r : Rep σ P) (s : Rep σ Q) : Rep σ (fun v => P v ∧ Q v) := by
  let left := r.expression.rename (Sum.map id (Fin.castAdd s.witnessCount))
  let right := s.expression.rename (Sum.map id (Fin.natAdd r.witnessCount))
  refine ⟨r.witnessCount + s.witnessCount, left * left + right * right, ?_⟩
  intro v
  simp only [left, right, Expr.eval_add, Expr.eval_mul, Expr.eval_rename,
    assignment_comp, Function.comp_id, mul_self_add_mul_self_eq_zero]
  exact (and_congr (r.correct v) (s.correct v)).trans (exists_fin_add_and _ _).symm

def disjunctionShort (r : Rep σ P) (s : Rep σ Q) : Rep σ (fun v => P v ∨ Q v) := by
  let left := r.expression.rename (Sum.map id (Fin.castAdd s.witnessCount))
  let right := s.expression.rename (Sum.map id (Fin.natAdd r.witnessCount))
  refine ⟨r.witnessCount + s.witnessCount, left * right, ?_⟩
  intro v
  simp only [left, right, Expr.eval_mul, Expr.eval_rename,
    assignment_comp, Function.comp_id, mul_eq_zero]
  exact (or_congr (r.correct v) (s.correct v)).trans (exists_fin_add_or _ _).symm

/-- Stronger than matching syntax and count separately: equality of all data. -/
theorem reindexShort_eq {τ : Type*} (r : Rep σ P) (f : σ → τ) :
    reindexShort r f = r.reindex f := rfl

theorem conjunctionShort_eq (r : Rep σ P) (s : Rep σ Q) :
    conjunctionShort r s = r.conjunction s := rfl

theorem disjunctionShort_eq (r : Rep σ P) (s : Rep σ Q) :
    disjunctionShort r s = r.disjunction s := rfl

theorem conjunctionShort_witnessCount (r : Rep σ P) (s : Rep σ Q) :
    (conjunctionShort r s).witnessCount = (r.conjunction s).witnessCount := rfl

theorem disjunctionShort_witnessCount (r : Rep σ P) (s : Rep σ Q) :
    (disjunctionShort r s).witnessCount = (r.disjunction s).witnessCount := rfl

theorem conjunctionShort_expression (r : Rep σ P) (s : Rep σ Q) :
    (conjunctionShort r s).expression = (r.conjunction s).expression := rfl

theorem disjunctionShort_expression (r : Rep σ P) (s : Rep σ Q) :
    (disjunctionShort r s).expression = (r.disjunction s).expression := rfl

#print axioms reindexShort
#print axioms conjunctionShort
#print axioms disjunctionShort
#print axioms conjunctionShort_eq
#print axioms disjunctionShort_eq

end RefactorPrototype
