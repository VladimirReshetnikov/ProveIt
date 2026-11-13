import DiophantineConsistency.Current14Carrier65DAGValue
import DiophantineConsistency.CurrentEquationSyntax2011

/-! Candidate composition: a counted circuit evaluates the current expression.
The value theorem has a checked provider; the expression-evaluation lemma is
replayed from ObjectCurrentEquation2011 because its object is not on this
provider path. This client itself has not yet been checked. -/
namespace DiophantineConsistency.Current14Carrier65DAG
open ArithmeticDAG

theorem expression_eval_eq_carrier {R : Type*} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (ObjectCurrentEquation2011.expressionAt p).evalRing v =
      Carrier65.value (fun j => (p j : R)) v := by
  simp only [ObjectCurrentEquation2011.expressionAt, Expr.evalRing_add,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    Carrier65.value, Carrier65.core]

theorem value_eq_expression {R : Type*} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    value nodes output (fun j => (p j : R)) v =
      (ObjectCurrentEquation2011.expressionAt p).evalRing v := by
  calc
    value nodes output (fun j => (p j : R)) v =
        Carrier65.value (fun j => (p j : R)) v := value_eq_carrier _ _
    _ = (ObjectCurrentEquation2011.expressionAt p).evalRing v :=
      (expression_eval_eq_carrier p v).symm

theorem circuit_realizes_expression {R : Type*} [CommRing R]
    (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    Topological nodes ∧ operationCount nodes = 65 ∧
      liveOperationCount nodes output = 65 ∧
      kindCount nodes 3 = 16 ∧ kindCount nodes 4 = 12 ∧
      kindCount nodes 5 = 37 ∧
      value nodes output (fun j => (p j : R)) v =
        (ObjectCurrentEquation2011.expressionAt p).evalRing v := by
  exact ⟨topological, operation_count, live_operation_count, addition_count,
    subtraction_count, multiplication_count, value_eq_expression p v⟩

end DiophantineConsistency.Current14Carrier65DAG

#print axioms DiophantineConsistency.Current14Carrier65DAG.expression_eval_eq_carrier
#print axioms DiophantineConsistency.Current14Carrier65DAG.value_eq_expression
#print axioms DiophantineConsistency.Current14Carrier65DAG.circuit_realizes_expression
