import DiophantineConsistency.NaturalRegisterProgram

/-! # Explicit existential scopes for shared natural-register relations -/

namespace DiophantineConsistency.NaturalRegisterRelation

open NaturalRegisterProgram

/-- Split the explicit source-input and auxiliary-input blocks. -/
def splitIndex (inputs auxiliary : ℕ) : Fin (inputs + auxiliary) → Fin inputs ⊕ Fin auxiliary :=
  Fin.addCases Sum.inl Sum.inr

theorem merge_split (v : Fin n → ℕ) (w : Fin k → ℕ) :
    Sum.elim v w ∘ splitIndex n k = Fin.addCases v w := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [splitIndex]

/-- Hide explicit auxiliary circuit inputs as natural existential witnesses. -/
def scopedEqualityRep {n k : ℕ} (p : Program (n + k)) (left right : Fin p.nodes.length) :
    Rep (Fin n) (fun v => ∃ a : Fin k → ℕ,
      p.eval (Fin.addCases v a) left = p.eval (Fin.addCases v a) right) := by
  let r := (p.equalityRep left right).reindex (splitIndex n k)
  refine r.existsBlock.ofIff ?_
  intro v
  simp only [merge_split]

@[simp] theorem scopedEqualityRep_witnessCount {n k : ℕ} (p : Program (n + k))
    (left right : Fin p.nodes.length) :
    (scopedEqualityRep p left right).witnessCount = k + p.nodes.length := rfl

theorem scopedEqualityRep_binaryOps {n k : ℕ} (p : Program (n + k))
    (left right : Fin p.nodes.length) :
    (scopedEqualityRep p left right).expression.binaryOps ≤ 6 * p.nodes.length + 4 := by
  simpa only [scopedEqualityRep,Rep.ofIff,Rep.existsBlock,Rep.reindex,Expr.binaryOps_rename]
    using p.equalityRep_binaryOps left right

theorem rename_toPolynomial {σ τ : Type*} (e : Expr σ) (f : σ → τ) :
    (e.rename f).toPolynomial = MvPolynomial.rename f e.toPolynomial := by
  induction e <;> simp_all [Expr.rename,Expr.toPolynomial]

theorem scopedEqualityRep_degree {n k : ℕ} (p : Program (n + k))
    (left right : Fin p.nodes.length) :
    (scopedEqualityRep p left right).expression.toPolynomial.totalDegree ≤ 4 := by
  simp only [scopedEqualityRep,Rep.ofIff,Rep.existsBlock,Rep.reindex,rename_toPolynomial]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    ((MvPolynomial.totalDegree_rename_le _ _).trans (p.equalityRep_degree left right))

/-- Supplied circuit data and a checked existential relation specification. -/
structure Relation (inputs : ℕ) (P : (Fin inputs → ℕ) → Prop) where
  auxiliaryCount : ℕ
  program : Program (inputs + auxiliaryCount)
  left : Fin program.nodes.length
  right : Fin program.nodes.length
  correct : ∀ v, P v ↔ ∃ a : Fin auxiliaryCount → ℕ,
    program.eval (Fin.addCases v a) left = program.eval (Fin.addCases v a) right

namespace Relation

variable {n : ℕ} {P : (Fin n → ℕ) → Prop}

/-- The final expression compiler introduces only local gate witnesses. -/
def compile (r : Relation n P) : Rep (Fin n) P :=
  (scopedEqualityRep r.program r.left r.right).ofIff (fun v => (r.correct v).symm)

@[simp] theorem compile_witnessCount (r : Relation n P) :
    r.compile.witnessCount = r.auxiliaryCount + r.program.nodes.length := rfl

theorem compile_binaryOps (r : Relation n P) :
    r.compile.expression.binaryOps ≤ 6 * r.program.nodes.length + 4 :=
  scopedEqualityRep_binaryOps r.program r.left r.right

theorem compile_degree (r : Relation n P) :
    r.compile.expression.toPolynomial.totalDegree ≤ 4 :=
  scopedEqualityRep_degree r.program r.left r.right

end Relation

end DiophantineConsistency.NaturalRegisterRelation
