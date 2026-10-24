import DiophantineConsistency.ObjectZeroTest

/-! # The literal shared conditional quartic on all internal naturals -/
noncomputable section
namespace DiophantineConsistency.ObjectConditional
open SetTheory ObjectOmegaSemiring NaturalRegisterProgram QuadraticRegisterSystem

private def zeroPort : Fin 3 → Slot QuadraticBoolean.conditionalProgram := ![.inl 4,.inl 1,.inl 5]
private theorem literal_system : QuadraticBoolean.conditionalSystem=
    (QuadraticBoolean.zeroSystem.instantiate QuadraticBoolean.conditionalProgram zeroPort).conjunction
      QuadraticBoolean.selectionSystem := rfl
private theorem literal_selection : QuadraticBoolean.selectionSystem.row (0 : Fin 1)=
    Expr.sub (.var (.inl (0 : Fin 6)))
      (.add (.mul (.var (.inl 4)) (.var (.inl 2)))
        (.mul (.sub (.constant 1) (.var (.inl 4))) (.var (.inl 3)))) := rfl

universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

def Certificate (out n zero positive bit slack : N H) : Prop :=
  ObjectZeroTest.Certificate H bit n slack ∧ out+bit*positive=bit*zero+positive

theorem certificate_sound {out n zero positive bit slack : N H}
    (h : Certificate H out n zero positive bit slack) : out=if n=0 then zero else positive := by
  have hb := ObjectZeroTest.certificate_sound H h.1
  have he := h.2
  by_cases hn : n=0
  · have hb1 : bit=1 := by simpa only [if_pos hn] using hb
    rw [hb1,one_mul,one_mul] at he
    simpa only [if_pos hn] using add_right_cancel he
  · have hb0 : bit=0 := by simpa only [if_neg hn] using hb
    simpa only [hb0,zero_mul,zero_add,add_zero,if_neg hn] using he

theorem certificate_complete (n zero positive : N H) :
    Certificate H (if n=0 then zero else positive) n zero positive
      (if n=0 then 1 else 0) (ObjectPredecessor.pred H n) := by
  refine ⟨ObjectZeroTest.certificate_complete H n,?_⟩
  by_cases hn : n=0 <;> simp [hn]

private theorem selection_zero_iff (x : Fin 6 → N H) :
    ObjectQuadraticSystem.RowsZero H QuadraticBoolean.selectionSystem (Sum.elim x Fin.elim0) ↔
      x 0+x 4*x 3=x 4*x 2+x 3 := by
  change (∀ i : Fin 1,(QuadraticBoolean.selectionSystem.row i).SemiringZero (Sum.elim x Fin.elim0)) ↔ _
  have hh : (QuadraticBoolean.selectionSystem.row (0 : Fin 1)).SemiringZero (Sum.elim x Fin.elim0) ↔
      x 0+x 4*x 3=x 4*x 2+x 3 := by
    rw [literal_selection]
    simp [Expr.SemiringZero,Expr.splitNatural,NatExpr.evalSemiring,Sum.elim]
  constructor
  · intro h
    exact hh.mp (h 0)
  · intro h i
    have hi : i=0 := Fin.eq_zero i
    exact hi ▸ hh.mpr h

theorem rows_zero_iff (x : Fin 6 → N H) :
    ObjectQuadraticSystem.RowsZero H QuadraticBoolean.conditionalSystem (Sum.elim x Fin.elim0) ↔
      Certificate H (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
  rw [literal_system,ObjectQuadraticSystem.conjunction_rows_zero_iff,
    ObjectQuadraticSystem.instantiate_rows_zero_iff]
  exact and_congr (ObjectZeroTest.rows_zero_iff H _) (selection_zero_iff H x)

def expression : Expr (Fin 6) := ObjectQuadraticSystem.inputExpression QuadraticBoolean.conditionalSystem
theorem expression_degree : expression.toPolynomial.totalDegree≤4 :=
  ObjectQuadraticSystem.inputExpression_degree _
theorem expression_zero_iff (x : Fin 6 → N H) : expression.SemiringZero x ↔
    Certificate H (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) :=
  (ObjectQuadraticSystem.inputExpression_zero_iff H _ x).trans (rows_zero_iff H x)

theorem exists_expression_zero_iff (out n zero positive : N H) :
    (∃ bit slack,expression.SemiringZero (![out,n,zero,positive,bit,slack] : Fin 6 → N H)) ↔
      out=if n=0 then zero else positive := by
  constructor
  · rintro ⟨bit,slack,h⟩
    exact certificate_sound H ((expression_zero_iff H _).mp h)
  · intro h
    exact ⟨if n=0 then 1 else 0,ObjectPredecessor.pred H n,
      (expression_zero_iff H _).mpr (h ▸ certificate_complete H n zero positive)⟩

end DiophantineConsistency.ObjectConditional
