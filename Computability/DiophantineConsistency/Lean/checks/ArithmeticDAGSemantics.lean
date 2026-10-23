import DiophantineConsistency.ArithmeticDAGSemantics
open DiophantineConsistency.ArithmeticDAG
#print axioms Node.eval_eq_evalAt
#print axioms Node.evalAt_congr
#print axioms run_length
#print axioms run_append
#print axioms run_preserves_getD
#print axioms run_node_equation
#print axioms run_eq_of_node_equations
#print axioms value_eq_of_node_equations

-- The multiplication-node equation follows from topology and the generic semantics.
example (p : Fin 1 → ℤ) (x : Fin 1 → ℤ) :
    let ns : List (Node 1 1) := [.input 0,.constant 0,.mul 0 1]
    (run p x ns []).getD 2 0 = (run p x ns []).getD 0 0 * (run p x ns []).getD 1 0 := by
  intro ns
  exact run_node_equation p x ns (by decide) 2 (by decide)
