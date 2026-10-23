import DiophantineConsistency.QuarticSyntax

/-! # Explicit tree-operation bounds for the gate quartic -/

namespace DiophantineConsistency.Expr

variable {σ τ : Type*}

/-- Binary arithmetic operations in the syntax tree, with constants and
variables charged zero. This is a tree bound, not a claimed optimal DAG. -/
def binaryOps : Expr σ → ℕ
  | .constant _ | .var _ => 0
  | .add p q | .sub p q | .mul p q => 1 + binaryOps p + binaryOps q

@[simp] theorem binaryOps_rename (e : Expr σ) (f : σ → τ) :
    (e.rename f).binaryOps = e.binaryOps := by
  induction e <;> simp_all [rename,binaryOps]

@[simp] theorem binaryOps_subst_atoms (e : Expr σ) (f : σ → Expr τ)
    (hf : ∀ i, (f i).binaryOps = 0) : (e.subst f).binaryOps = e.binaryOps := by
  induction e <;> simp_all [subst,binaryOps]

end DiophantineConsistency.Expr

namespace DiophantineConsistency.QuarticCost

open QuarticCompiler

/-- A gate residual uses at most two binary operations. -/
theorem gate_residual_binaryOps {σ : Type*} (e : NatExpr σ) :
    ∀ k, (Gates.residualSyntax e k).binaryOps ≤ 2 := by
  induction e with
  | constant n => intro k; change 1 ≤ 2; decide
  | var i => intro k; change 1 ≤ 2; decide
  | add p q hp hq =>
      intro k
      cases k with
      | inl k => change 2 ≤ 2; decide
      | inr k =>
          cases k with
          | inl k => simpa only [Gates.residualSyntax,Expr.binaryOps_rename] using hp k
          | inr k => simpa only [Gates.residualSyntax,Expr.binaryOps_rename] using hq k
  | mul p q hp hq =>
      intro k
      cases k with
      | inl k => change 2 ≤ 2; decide
      | inr k =>
          cases k with
          | inl k => simpa only [Gates.residualSyntax,Expr.binaryOps_rename] using hp k
          | inr k => simpa only [Gates.residualSyntax,Expr.binaryOps_rename] using hq k

/-- Includes the output equality and normalization guard. -/
theorem residual_binaryOps {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m))
    (i : Equation p q) : (residualSyntax p q i).binaryOps ≤ 2 := by
  cases i with
  | inl i => change 1 ≤ 2; decide
  | inr i =>
      cases i with
      | inl k => simpa only [residualSyntax,Expr.binaryOps_rename] using gate_residual_binaryOps p k
      | inr i =>
          cases i with
          | inl k => simpa only [residualSyntax,Expr.binaryOps_rename] using gate_residual_binaryOps q k
          | inr i => change 1 ≤ 2; decide

theorem sumExpressions_binaryOps_le {σ : Type*} (es : List (Expr σ))
    (h : ∀ e ∈ es, e.binaryOps ≤ 5) :
    (QuarticSyntax.sumExpressions es).binaryOps ≤ 6 * es.length := by
  induction es with
  | nil => simp [QuarticSyntax.sumExpressions,Expr.binaryOps]
  | cons e es ih =>
      have he := h e (by simp)
      have hrest := ih (fun p hp => h p (by simp [hp]))
      change 1 + e.binaryOps + (QuarticSyntax.sumExpressions es).binaryOps ≤ 6 * (es.length + 1)
      omega

/-- The explicit syntax uses at most six operations per quadratic residual,
including its square and the sum accumulator. -/
theorem expression_binaryOps_le {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (QuarticSyntax.expression p q).binaryOps ≤
      6 * (Gates.count p + Gates.count q + 2) := by
  rw [QuarticSyntax.expression,Expr.binaryOps_rename]
  have h := sumExpressions_binaryOps_le
    (List.ofFn fun i =>
      let e := residualSyntax p q ((QuarticSyntax.equationIndex p q).symm i)
      e * e) (by
        intro e he
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
        have hbound := residual_binaryOps p q ((QuarticSyntax.equationIndex p q).symm i)
        change 1 + _ + _ ≤ 5
        omega)
  simp only [List.length_ofFn] at h
  exact h.trans (by omega)

end DiophantineConsistency.QuarticCost
