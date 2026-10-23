import DiophantineConsistency.DAGQuartic

open DiophantineConsistency ArithmeticDAG DAGQuartic

-- A genuinely shared, signed intermediate: (x-3)^2-1.
private def shared : List (Node 1 0) :=
  [.input 0,.literal 3,.sub 0 1,.mul 2 2,.literal 1,.sub 3 4]

private theorem shared_topological : Topological shared := by decide +kernel

example : value shared 5 Fin.elim0 (fun _ => (2 : ℤ)) = 0 := rfl

example : signedRead (witnesses shared Fin.elim0 (fun _ => 2)) 2 = -1 := rfl

example : witnesses shared Fin.elim0 (fun _ => 2) (.inl ⟨2,by decide⟩) = 0 := rfl
example : witnesses shared Fin.elim0 (fun _ => 2) (.inr ⟨2,by decide⟩) = 1 := rfl

example : ∃ w, (expression shared 5 Fin.elim0).eval (assignment (fun _ => 2) w) = 0 :=
  (exists_zero_iff shared shared_topological 5 (by decide) Fin.elim0 _).mpr rfl

-- A nonzero output is rejected, although gate witnesses are unconstrained naturals.
example : ¬ ∃ w, (expression shared 5 Fin.elim0).eval (assignment (fun _ => 3) w) = 0 := by
  rw [exists_zero_iff shared shared_topological 5 (by decide) Fin.elim0]
  decide

-- A self-reference is not a topological circuit.
example : ¬ Topological ([.mul 0 0] : List (Node 0 0)) := by decide +kernel

example : Fintype.card (Variables 1 shared.length) = 13 := rfl

example : (expression shared 5 Fin.elim0).binaryOps ≤ 76 :=
  expression_binaryOps shared 5 Fin.elim0

example : (DAGQuartic.polynomial shared 5 Fin.elim0).totalDegree ≤ 4 :=
  polynomial_degree shared 5 Fin.elim0

#print axioms expression_zero_iff
#print axioms signedRead_witnesses
#print axioms exists_zero_iff
#print axioms expression_binaryOps
#print axioms polynomial_degree
#print axioms variable_count
#print axioms exists_polynomial_zero_iff
