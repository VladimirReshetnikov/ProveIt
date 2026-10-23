import DiophantineConsistency.NaturalDAGQuartic

open DiophantineConsistency ArithmeticDAG NaturalDAGQuartic

-- A shared arithmetic circuit for (x+1)^2=9.
private def shared : List (Node 1 0) :=
  [.input 0,.literal 1,.add 0 1,.mul 2 2,.literal 9]

private theorem shared_topological : Topological shared := by decide +kernel
private theorem shared_allowed : Allowed shared Fin.elim0 := by decide +kernel

example : ∃ w, (expression shared 3 4 Fin.elim0).eval (assignment (fun _ => 2) w) = 0 :=
  (exists_zero_iff shared shared_topological 3 4 (by decide) (by decide)
    Fin.elim0 shared_allowed _).mpr rfl

example : ¬ ∃ w, (expression shared 3 4 Fin.elim0).eval (assignment (fun _ => 0) w) = 0 := by
  rw [exists_zero_iff shared shared_topological 3 4 (by decide) (by decide) Fin.elim0 shared_allowed]
  decide

example : Fintype.card (Variables 1 shared.length) = 6 := rfl
example : (expression shared 3 4 Fin.elim0).binaryOps = 28 := rfl
example : (expression shared 3 4 Fin.elim0).binaryOps ≤ 34 :=
  expression_binaryOps shared 3 4 Fin.elim0
example : (NaturalDAGQuartic.polynomial shared 3 4 Fin.elim0).totalDegree ≤ 4 :=
  polynomial_degree shared 3 4 Fin.elim0

-- The smaller compiler rejects signed constants and subtraction nodes.
-- The signed compiler is available when those values are required.
example : ¬ Allowed ([.literal (-1)] : List (Node 0 0)) Fin.elim0 := by decide +kernel
example : ¬ Allowed ([.input 0,.sub 0 0] : List (Node 1 0)) Fin.elim0 := by decide +kernel

#print axioms run_nonnegative
#print axioms expression_zero_iff
#print axioms read_witnesses
#print axioms exists_zero_iff
#print axioms expression_binaryOps
#print axioms polynomial_degree
#print axioms variable_count
#print axioms exists_polynomial_zero_iff
