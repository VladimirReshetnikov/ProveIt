import DiophantineConsistency.ArithmeticDAG
open DiophantineConsistency.ArithmeticDAG
#print axioms Node.eval_map
#print axioms run_map
#print axioms value_map
#print axioms eval_polynomial
#print axioms reaches_of_laterConsumer
#print axioms liveOperationCount_eq

example (p : Fin 1 → ℤ) (x : Fin 1 → ℤ) :
    value [.input 0,.constant 0,.mul 0 1] 2 p x = x 0*p 0 := rfl
example : Topological ([.input 0,.constant 0,.mul 0 1] : List (Node 1 1)) := by decide
example : operationCount ([.input 0,.constant 0,.mul 0 1] : List (Node 1 1)) = 1 := by decide
