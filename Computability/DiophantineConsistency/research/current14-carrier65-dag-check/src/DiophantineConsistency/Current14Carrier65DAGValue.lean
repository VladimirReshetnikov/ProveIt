import DiophantineConsistency.Current14Carrier65DAGCore
import DiophantineConsistency.Carrier65

namespace DiophantineConsistency.Current14Carrier65DAG
open ArithmeticDAG

/-- This is the essential bridge from the counted DAG to the maintained polynomial. -/
theorem value_eq_carrier {R : Type*} [CommRing R]
    (p : Fin 4 → R) (v : Fin 14 → R) :
    value nodes output p v = Carrier65.value p v := by
  simp only [value, output, nodes, run, Node.eval, List.getD,
    List.append, Carrier65.value, Carrier65.core, pow_succ, pow_zero,
    one_mul, mul_one, mul_assoc]

end DiophantineConsistency.Current14Carrier65DAG

#print axioms DiophantineConsistency.Current14Carrier65DAG.value_eq_carrier
