import DiophantineConsistency.ObjectNumericWire

/-! # Actual compositional tree-projection quartics on internal omega -/
noncomputable section
namespace DiophantineConsistency.ObjectTreeCodeSyntax
open SetTheory ObjectOmegaSemiring NaturalRegisterProgram QuadraticRegisterSystem

private def predPort : Fin 2 → Slot QuadraticTreeCodeGraphs.program := ![.inl 2,.inl 1]
private def leftPort : Fin 6 → Slot QuadraticTreeCodeGraphs.program :=
  ![.inl 0,.inl 2,.inl 3,.inl 4,.inl 5,.inl 6]
private def rightPort : Fin 6 → Slot QuadraticTreeCodeGraphs.program :=
  ![.inl 3,.inl 2,.inl 0,.inl 4,.inl 5,.inl 6]

private theorem literal_left : QuadraticTreeCodeGraphs.leftSystem=
    (QuadraticTreeCodeGraphs.predSystem.instantiate QuadraticTreeCodeGraphs.program predPort).conjunction
      ((QuadraticNatPairing.system 0 2).instantiate QuadraticTreeCodeGraphs.program leftPort) := rfl
private theorem literal_right : QuadraticTreeCodeGraphs.rightSystem=
    (QuadraticTreeCodeGraphs.predSystem.instantiate QuadraticTreeCodeGraphs.program predPort).conjunction
      ((QuadraticNatPairing.system 0 2).instantiate QuadraticTreeCodeGraphs.program rightPort) := rfl

universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

private theorem pred_rows (x : Fin 2 → N H) :
    ObjectQuadraticSystem.RowsZero H QuadraticTreeCodeGraphs.predSystem (Sum.elim x Fin.elim0) ↔
      x 0=ObjectPredecessor.pred H (x 1) :=
  (ObjectPredecessorSyntax.rows_zero_iff H x).trans (ObjectPredecessor.certificate_iff H _ _)

private theorem pair_rows (x : Fin 6 → N H) :
    ObjectQuadraticSystem.RowsZero H (QuadraticNatPairing.system 0 2) (Sum.elim x Fin.elim0) ↔
      ObjectNatPairing.Certificate H (x 1) (x 0) (x 2) (x 3) (x 4) (x 5) :=
  ObjectPairingSyntax.rows_zero_iff H x

theorem left_rows_zero_iff (x : Fin 7 → N H) :
    ObjectQuadraticSystem.RowsZero H QuadraticTreeCodeGraphs.leftSystem (Sum.elim x Fin.elim0) ↔
      x 2=ObjectPredecessor.pred H (x 1) ∧
        ObjectNatPairing.Certificate H (x 2) (x 0) (x 3) (x 4) (x 5) (x 6) := by
  rw [literal_left,ObjectQuadraticSystem.conjunction_rows_zero_iff,
    ObjectQuadraticSystem.instantiate_rows_zero_iff,ObjectQuadraticSystem.instantiate_rows_zero_iff]
  exact and_congr (pred_rows H _) (pair_rows H _)

theorem right_rows_zero_iff (x : Fin 7 → N H) :
    ObjectQuadraticSystem.RowsZero H QuadraticTreeCodeGraphs.rightSystem (Sum.elim x Fin.elim0) ↔
      x 2=ObjectPredecessor.pred H (x 1) ∧
        ObjectNatPairing.Certificate H (x 2) (x 3) (x 0) (x 4) (x 5) (x 6) := by
  rw [literal_right,ObjectQuadraticSystem.conjunction_rows_zero_iff,
    ObjectQuadraticSystem.instantiate_rows_zero_iff,ObjectQuadraticSystem.instantiate_rows_zero_iff]
  exact and_congr (pred_rows H _) (pair_rows H _)

theorem left_rows_sound (x : Fin 7 → N H)
    (h : ObjectQuadraticSystem.RowsZero H QuadraticTreeCodeGraphs.leftSystem (Sum.elim x Fin.elim0)) :
    x 0=ObjectNumericWire.treeLeft H (x 1) := by
  obtain ⟨hp,hc⟩ := (left_rows_zero_iff H x).mp h
  have he : ObjectPredecessor.pred H (x 1)=ObjectNatPairing.pair H (x 0) (x 3) :=
    hp ▸ ObjectNatPairing.certificate_sound H hc
  rw [ObjectNumericWire.treeLeft,he,ObjectUnpair.unpair_pair]

theorem right_rows_sound (x : Fin 7 → N H)
    (h : ObjectQuadraticSystem.RowsZero H QuadraticTreeCodeGraphs.rightSystem (Sum.elim x Fin.elim0)) :
    x 0=ObjectNumericWire.treeRight H (x 1) := by
  obtain ⟨hp,hc⟩ := (right_rows_zero_iff H x).mp h
  have he : ObjectPredecessor.pred H (x 1)=ObjectNatPairing.pair H (x 3) (x 0) :=
    hp ▸ ObjectNatPairing.certificate_sound H hc
  rw [ObjectNumericWire.treeRight,he,ObjectUnpair.unpair_pair]

def leftExpression : Expr (Fin 7) :=
  ObjectQuadraticSystem.inputExpression QuadraticTreeCodeGraphs.leftSystem
def rightExpression : Expr (Fin 7) :=
  ObjectQuadraticSystem.inputExpression QuadraticTreeCodeGraphs.rightSystem

theorem left_degree : leftExpression.toPolynomial.totalDegree≤4 :=
  ObjectQuadraticSystem.inputExpression_degree _
theorem right_degree : rightExpression.toPolynomial.totalDegree≤4 :=
  ObjectQuadraticSystem.inputExpression_degree _

theorem left_expression_zero_iff (x : Fin 7 → N H) : leftExpression.SemiringZero x ↔
    x 2=ObjectPredecessor.pred H (x 1) ∧
      ObjectNatPairing.Certificate H (x 2) (x 0) (x 3) (x 4) (x 5) (x 6) :=
  (ObjectQuadraticSystem.inputExpression_zero_iff H _ x).trans (left_rows_zero_iff H x)
theorem right_expression_zero_iff (x : Fin 7 → N H) : rightExpression.SemiringZero x ↔
    x 2=ObjectPredecessor.pred H (x 1) ∧
      ObjectNatPairing.Certificate H (x 2) (x 3) (x 0) (x 4) (x 5) (x 6) :=
  (ObjectQuadraticSystem.inputExpression_zero_iff H _ x).trans (right_rows_zero_iff H x)

theorem exists_left_zero_iff (out code : N H) :
    (∃ w : Fin 5 → N H,leftExpression.SemiringZero
      (![out,code,w 0,w 1,w 2,w 3,w 4] : Fin 7 → N H)) ↔
        out=ObjectNumericWire.treeLeft H code := by
  constructor
  · rintro ⟨w,hw⟩
    exact left_rows_sound H _ ((ObjectQuadraticSystem.inputExpression_zero_iff H _ _).mp hw)
  · intro h
    have hp : ObjectPredecessor.pred H code=ObjectNatPairing.pair H out
        (ObjectUnpair.unpair H (ObjectPredecessor.pred H code)).2 := by
      rw [h,ObjectNumericWire.treeLeft,ObjectUnpair.pair_unpair]
    obtain ⟨t,s,m,hc⟩ := ObjectNatPairing.certificate_complete H hp
    exact ⟨![ObjectPredecessor.pred H code,
      (ObjectUnpair.unpair H (ObjectPredecessor.pred H code)).2,t,s,m],
        (left_expression_zero_iff H _).mpr ⟨rfl,hc⟩⟩

theorem exists_right_zero_iff (out code : N H) :
    (∃ w : Fin 5 → N H,rightExpression.SemiringZero
      (![out,code,w 0,w 1,w 2,w 3,w 4] : Fin 7 → N H)) ↔
        out=ObjectNumericWire.treeRight H code := by
  constructor
  · rintro ⟨w,hw⟩
    exact right_rows_sound H _ ((ObjectQuadraticSystem.inputExpression_zero_iff H _ _).mp hw)
  · intro h
    have hp : ObjectPredecessor.pred H code=ObjectNatPairing.pair H
        (ObjectUnpair.unpair H (ObjectPredecessor.pred H code)).1 out := by
      rw [h,ObjectNumericWire.treeRight,ObjectUnpair.pair_unpair]
    obtain ⟨t,s,m,hc⟩ := ObjectNatPairing.certificate_complete H hp
    exact ⟨![ObjectPredecessor.pred H code,
      (ObjectUnpair.unpair H (ObjectPredecessor.pred H code)).1,t,s,m],
        (right_expression_zero_iff H _).mpr ⟨rfl,hc⟩⟩

end DiophantineConsistency.ObjectTreeCodeSyntax
