import DiophantineConsistency.ArithmeticDAGSemantics
import DiophantineConsistency.GapCircuit66

/-! On-demand specialization of the existing local-node theorem.
This prototype deliberately leaves named semantic cut points in place.
It is not a global simp rule: unbounded recursive rewriting would inline the DAG.
-/
namespace DiophantineConsistency.ProofSimplification.CircuitDispatch
open ArithmeticDAG
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

variable {R : Type*} [CommRing R]

def reg (p : Fin 11 → R) (x : Fin 9 → R) (i : ℕ) : R :=
  value GapCircuit66.naturalNodes i p x

theorem step (p : Fin 11 → R) (x : Fin 9 → R) (i : ℕ) (hi : i < 484) :
    reg p x i = (GapCircuit66.naturalNodes.getD i (.literal 0)).evalAt p x (reg p x) :=
  run_node_equation p x GapCircuit66.naturalNodes GapCircuit66.natural_topological i
    (by simpa only [GapCircuit66.natural_length] using hi)

-- The statement has exactly the same content as natural_step_20.
example (p : Fin 11 → R) (x : Fin 9 → R) :
    reg p x 20 = reg p x 18 * reg p x 19 :=
  step p x 20 (by decide)

-- Selective specialization keeps the base as the intended cut point.
theorem base_identity (p : Fin 11 → R) (x : Fin 9 → R) :
    reg p x 20 = p 0 * (x 0 + 1)^2 := by
  simp only [step p x 20 (by decide), step p x 18 (by decide),
    step p x 19 (by decide), step p x 10 (by decide),
    step p x 0 (by decide), step p x 9 (by decide),
    GapCircuit66.naturalNodes, List.getD_cons_zero, List.getD_cons_succ, Node.evalAt, Fin.mk_zero]
  ring

#print axioms base_identity
end DiophantineConsistency.ProofSimplification.CircuitDispatch
