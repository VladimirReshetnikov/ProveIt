import DiophantineConsistency.ObjectDivision
import DiophantineConsistency.QuadraticDivMod

/-! # The literal guarded div/mod quartic on all internal naturals -/
noncomputable section
namespace DiophantineConsistency.ObjectDivModSyntax
open SetTheory ObjectOmegaSemiring

private theorem literal_row0 : QuadraticDivMod.rows 0=
    Expr.sub (.var (.inl (2 : Fin 5)))
      (.add (.mul (.var (.inl 0)) (.var (.inl 3))) (.var (.inl 1))) := rfl
private theorem literal_row1 : QuadraticDivMod.rows 1=
    Expr.sub (.var (.inl (3 : Fin 5)))
      (.add (.add (.var (.inl 1)) (.var (.inl 4))) (.constant 1)) := rfl

universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

theorem rows_zero_iff (x : Fin 5 → N H) :
    ObjectQuadraticSystem.RowsZero H QuadraticDivMod.system (Sum.elim x Fin.elim0) ↔
      x 2=x 0*x 3+x 1 ∧ x 3=x 1+x 4+1 := by
  change (∀ i : Fin 2,(QuadraticDivMod.rows i).SemiringZero (Sum.elim x Fin.elim0)) ↔ _
  have h0 : (QuadraticDivMod.rows 0).SemiringZero (Sum.elim x Fin.elim0) ↔
      x 2=x 0*x 3+x 1 := by
    rw [literal_row0]
    simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,Sum.elim]
  have h1 : (QuadraticDivMod.rows 1).SemiringZero (Sum.elim x Fin.elim0) ↔
      x 3=x 1+x 4+1 := by
    rw [literal_row1]
    simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,Sum.elim]
  constructor
  · intro h
    exact ⟨h0.mp (h 0),h1.mp (h 1)⟩
  · intro h i
    fin_cases i
    · exact h0.mpr h.1
    · exact h1.mpr h.2

def expression : Expr (Fin 5) := ObjectQuadraticSystem.inputExpression QuadraticDivMod.system
theorem expression_degree : expression.toPolynomial.totalDegree≤4 :=
  ObjectQuadraticSystem.inputExpression_degree _
theorem expression_zero_iff (x : Fin 5 → N H) : expression.SemiringZero x ↔
    x 2=x 0*x 3+x 1 ∧ x 3=x 1+x 4+1 :=
  (ObjectQuadraticSystem.inputExpression_zero_iff H _ x).trans (rows_zero_iff H x)

/-- Zero denominators have no certificate. No side premise is supplied. -/
theorem exists_expression_zero_iff (q r n d : N H) :
    (∃ s,expression.SemiringZero (![q,r,n,d,s] : Fin 5 → N H)) ↔
      0<d ∧ ObjectDivision.divmod H n d=(q,r) := by
  simpa [expression_zero_iff] using ObjectDivision.exists_certificate_iff H q r n d

end DiophantineConsistency.ObjectDivModSyntax
