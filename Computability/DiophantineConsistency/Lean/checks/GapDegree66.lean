import DiophantineConsistency.GapPolynomialDegree66

open DiophantineConsistency

-- Invalid labels must fail even though a circuit's output could cancel.
example : ¬ ArithmeticDAG.DegreeCertificate GapCircuit66.naturalNodes
    (fun _ => 1) (fun _ => 0) := by decide +kernel

private def cancellation : List (ArithmeticDAG.Node 1 0) := [.input 0,.sub 0 0]
example : ArithmeticDAG.DegreeCertificate cancellation (fun _ => 1) (fun _ => 1) := by
  decide +kernel

-- A certified upper bound need not be the exact degree.
example : ArithmeticDAG.polynomial cancellation 1 Fin.elim0=0 := by
  simp [ArithmeticDAG.polynomial,ArithmeticDAG.value,ArithmeticDAG.run,
    ArithmeticDAG.Node.eval,cancellation]

example (p : Fin 11 → ℤ) :
    (GapCircuit66.naturalPolynomial p).totalDegree ≤ 1845940 :=
  GapFinalizerDegree66.naturalPolynomial_degree_le p

example (p : Fin 11 → ℤ) :
    (GapCircuit66.naturalValue (fun k => MvPolynomial.C (p k))
      (fun i : Fin 9 => MvPolynomial.X i-1)).totalDegree ≤ 1845940 := by
  apply GapFinalizerDegree66.naturalValue_degree_le
  intro i
  exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)

#print axioms ArithmeticDAG.Node.evalAt_degree_le
#print axioms ArithmeticDAG.value_degree_le
#print axioms ArithmeticDAG.polynomial_degree_le
#print axioms Expr.evalRing_X
#print axioms Expr.degree_evalRing_le
#print axioms FreeCarrierDegree.defect_weightedDegree
#print axioms FreeCarrierDegree.inner_weightedDegree
#print axioms FreeCarrierDegree.norm_weightedDegree
#print axioms FreeCarrierDegree.eval_normSyntax
#print axioms FreeCarrierDegree.defect_degree_le
#print axioms FreeCarrierDegree.norm_degree_le
#print axioms GapCircuitDegree66.naturalDegrees_length
#print axioms GapCircuitDegree66.natural_certificate
#print axioms GapCircuitDegree66.naturalRegister_degree_le
#print axioms GapCircuitDegree66.naturalPolynomial_degree_le_naive
#print axioms GapCircuitTail66.natural_pell_DF
#print axioms GapCircuitTail66.natural_pell_I
#print axioms GapFinalizerDegree66.natural_majorant
#print axioms GapFinalizerDegree66.natural_radicand0
#print axioms GapFinalizerDegree66.natural_radicand1
#print axioms GapFinalizerDegree66.natural_theta
#print axioms GapCircuitTail66.natural_tail_output
#print axioms GapFinalizerDegree66.naturalValue_degree_le
#print axioms GapFinalizerDegree66.naturalPolynomial_degree_le
#print axioms GapPolynomialDegree66.positivePolynomial_degree_le
#print axioms GapPolynomialDegree66.sourcePolynomial_degree_le
#print axioms GapPolynomialDegree66.positiveSourcePolynomial_degree_le
