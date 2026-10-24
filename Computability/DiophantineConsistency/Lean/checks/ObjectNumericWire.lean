import DiophantineConsistency.ObjectTreeCodeSyntax
import DiophantineConsistency.ObjectZeroTest

open DiophantineConsistency SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency

example : BProv ZFCax_s [] ObjectPredecessorSyntax.totalForm :=
  ObjectPredecessorSyntax.zfc_proves_total
example : ObjectTreeCodeSyntax.leftExpression.toPolynomial.totalDegree≤4 :=
  ObjectTreeCodeSyntax.left_degree
example : ObjectTreeCodeSyntax.rightExpression.toPolynomial.totalDegree≤4 :=
  ObjectTreeCodeSyntax.right_degree
example : ObjectZeroTest.expression.toPolynomial.totalDegree≤4 := ObjectZeroTest.expression_degree

example {V : Type} {mem : V → V → Prop} (H : ZFAxioms mem)
    (code : ObjectOmegaSemiring.Natural H) :
    ∃ w : Fin 5 → ObjectOmegaSemiring.Natural H,
      ObjectTreeCodeSyntax.leftExpression.SemiringZero
        ![ObjectNumericWire.treeLeft H code,code,w 0,w 1,w 2,w 3,w 4] :=
  (ObjectTreeCodeSyntax.exists_left_zero_iff H _ code).mpr rfl

#print axioms ObjectPredecessor.pred_zero
#print axioms ObjectPredecessor.pred_spec
#print axioms ObjectPredecessor.pred_add_one
#print axioms ObjectPredecessor.pred_cast
#print axioms ObjectPredecessor.certificate_iff
#print axioms ObjectQuadraticSystem.conjunction_rows_zero_iff
#print axioms ObjectQuadraticSystem.instantiate_rows_zero_iff
#print axioms ObjectQuadraticSystem.expression_zero_iff
#print axioms ObjectQuadraticSystem.empty_expression_zero_iff
#print axioms ObjectQuadraticSystem.inputExpression_degree
#print axioms ObjectQuadraticSystem.inputExpression_zero_iff
#print axioms ObjectPredecessorSyntax.rows_zero_iff
#print axioms ObjectPredecessorSyntax.expression_degree
#print axioms ObjectPredecessorSyntax.expression_zero_iff
#print axioms ObjectPredecessorSyntax.graphForm_spec
#print axioms ObjectPredecessorSyntax.sentence_totalForm
#print axioms ObjectPredecessorSyntax.zfc_proves_total
#print axioms ObjectNumericWire.left_cons
#print axioms ObjectNumericWire.right_cons
#print axioms ObjectNumericWire.head_cons
#print axioms ObjectNumericWire.tail_cons
#print axioms ObjectNumericWire.head_zero
#print axioms ObjectNumericWire.tail_zero
#print axioms ObjectNumericWire.zero_or_cons
#print axioms ObjectNumericWire.cons_eq_cons_iff
#print axioms ObjectNumericWire.left_cast
#print axioms ObjectNumericWire.right_cast
#print axioms ObjectTreeCodeSyntax.left_rows_zero_iff
#print axioms ObjectTreeCodeSyntax.right_rows_zero_iff
#print axioms ObjectTreeCodeSyntax.left_rows_sound
#print axioms ObjectTreeCodeSyntax.right_rows_sound
#print axioms ObjectTreeCodeSyntax.left_degree
#print axioms ObjectTreeCodeSyntax.right_degree
#print axioms ObjectTreeCodeSyntax.exists_left_zero_iff
#print axioms ObjectTreeCodeSyntax.exists_right_zero_iff
#print axioms ObjectZeroTest.certificate_sound
#print axioms ObjectZeroTest.certificate_complete
#print axioms ObjectZeroTest.exists_certificate_iff
#print axioms ObjectZeroTest.rows_zero_iff
#print axioms ObjectZeroTest.expression_degree
#print axioms ObjectZeroTest.expression_zero_iff
#print axioms ObjectZeroTest.exists_expression_zero_iff
