import DiophantineConsistency.ObjectConditional
import DiophantineConsistency.ObjectListHead

open DiophantineConsistency SetTheory

example : ObjectConditional.expression.toPolynomial.totalDegree≤4 := ObjectConditional.expression_degree
example : ObjectListHead.expression.toPolynomial.totalDegree≤4 := ObjectListHead.expression_degree

example {V : Type} {mem : V → V → Prop} (H : ZFAxioms mem)
    (code : ObjectOmegaSemiring.Natural H) :
    ∃ w : Fin 7 → ObjectOmegaSemiring.Natural H,
      ObjectListHead.expression.SemiringZero
        ![ObjectNumericWire.listHead H code,code,w 0,w 1,w 2,w 3,w 4,w 5,w 6] :=
  (ObjectListHead.exists_expression_zero_iff H _ code).mpr rfl

#print axioms ObjectConditional.certificate_sound
#print axioms ObjectConditional.certificate_complete
#print axioms ObjectConditional.rows_zero_iff
#print axioms ObjectConditional.expression_degree
#print axioms ObjectConditional.expression_zero_iff
#print axioms ObjectConditional.exists_expression_zero_iff
#print axioms ObjectListHead.left_le_pair
#print axioms ObjectListHead.listHead_le
#print axioms ObjectListHead.guard_sound
#print axioms ObjectListHead.guard_complete
#print axioms ObjectListHead.rows_zero_iff
#print axioms ObjectListHead.expression_degree
#print axioms ObjectListHead.expression_zero_iff
#print axioms ObjectListHead.exists_expression_zero_iff
