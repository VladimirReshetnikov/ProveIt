import DiophantineConsistency.ObjectNumericWire
import DiophantineConsistency.QuadraticBoolean

/-! # Literal Boolean zero-test rows on the entire internal omega -/
noncomputable section
namespace DiophantineConsistency.ObjectZeroTest
set_option maxRecDepth 16000
open SetTheory ObjectOmegaSemiring

private theorem literal_row0 : QuadraticBoolean.zeroRows 0=
    Expr.mul (.var (.inl (0 : Fin 3))) (.sub (.var (.inl 0)) (.constant 1)) := rfl
private theorem literal_row1 : QuadraticBoolean.zeroRows 1=
    Expr.mul (.var (.inl (0 : Fin 3))) (.var (.inl 1)) := rfl
private theorem literal_row2 : QuadraticBoolean.zeroRows 2=
    Expr.sub (.var (.inl (1 : Fin 3)))
      (.mul (.sub (.constant 1) (.var (.inl 0))) (.add (.var (.inl 2)) (.constant 1))) := rfl

universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

def Certificate (bit n slack : N H) : Prop :=
  bit*bit=bit ∧ bit*n=0 ∧ n+bit*(slack+1)=slack+1

theorem certificate_sound {bit n slack : N H} (h : Certificate H bit n slack) :
    bit=if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · have he : bit*(slack+1)=1*(slack+1) := by
      simpa only [hn,zero_add,one_mul] using h.2.2
    simpa only [if_pos hn] using
      mul_right_cancel₀ (ObjectNaturalDiscrete.add_one_ne_zero H slack) he
  · simpa only [if_neg hn] using (mul_eq_zero.mp h.2.1).resolve_right hn

theorem certificate_complete (n : N H) :
    Certificate H (if n=0 then 1 else 0) n (ObjectPredecessor.pred H n) := by
  by_cases hn : n=0
  · subst n
    simp [Certificate,ObjectPredecessor.pred_zero]
  · simpa [Certificate,hn] using ObjectPredecessor.pred_spec H n hn

theorem exists_certificate_iff (bit n : N H) :
    (∃ slack,Certificate H bit n slack) ↔ bit=if n=0 then 1 else 0 := by
  constructor
  · rintro ⟨s,hs⟩
    exact certificate_sound H hs
  · intro h
    exact ⟨ObjectPredecessor.pred H n,h ▸ certificate_complete H n⟩

theorem rows_zero_iff (x : Fin 3 → N H) :
    ObjectQuadraticSystem.RowsZero H QuadraticBoolean.zeroSystem (Sum.elim x Fin.elim0) ↔
      Certificate H (x 0) (x 1) (x 2) := by
  change (∀ i : Fin 3,(QuadraticBoolean.zeroRows i).SemiringZero (Sum.elim x Fin.elim0)) ↔ _
  have h0 : (QuadraticBoolean.zeroRows 0).SemiringZero (Sum.elim x Fin.elim0) ↔
      x 0*x 0=x 0 := by
    rw [literal_row0]
    simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,Sum.elim]
  have h1 : (QuadraticBoolean.zeroRows 1).SemiringZero (Sum.elim x Fin.elim0) ↔
      x 0*x 1=0 := by
    rw [literal_row1]
    simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,Sum.elim]
  have h2 : (QuadraticBoolean.zeroRows 2).SemiringZero (Sum.elim x Fin.elim0) ↔
      x 1+x 0*(x 2+1)=x 2+1 := by
    rw [literal_row2]
    simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,Sum.elim]
  constructor
  · intro h
    exact ⟨h0.mp (h 0),h1.mp (h 1),h2.mp (h 2)⟩
  · intro h i
    fin_cases i
    · exact h0.mpr h.1
    · exact h1.mpr h.2.1
    · exact h2.mpr h.2.2

def expression : Expr (Fin 3) := ObjectQuadraticSystem.inputExpression QuadraticBoolean.zeroSystem
theorem expression_degree : expression.toPolynomial.totalDegree≤4 :=
  ObjectQuadraticSystem.inputExpression_degree _

theorem expression_zero_iff (x : Fin 3 → N H) :
    expression.SemiringZero x ↔ Certificate H (x 0) (x 1) (x 2) :=
  (ObjectQuadraticSystem.inputExpression_zero_iff H _ x).trans (rows_zero_iff H x)

theorem exists_expression_zero_iff (bit n : N H) :
    (∃ slack,expression.SemiringZero (![bit,n,slack] : Fin 3 → N H)) ↔
      bit=if n=0 then 1 else 0 := by
  simpa [expression_zero_iff] using exists_certificate_iff H bit n

end DiophantineConsistency.ObjectZeroTest
