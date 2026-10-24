import DiophantineConsistency.AnnotatedSharedSyntax

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedSharedSyntax

example (t : Tree) : (graph t).witnessCount=4*AnnotatedSyntaxGraphs.forkCount t := graph_witnessCount t
example (t : Tree) : (graph t).expression.toPolynomial.totalDegree≤4 := graph_degree t
example (t : Tree) : (system t).rowCount=4*AnnotatedSyntaxGraphs.forkCount t+1 := system_rowCount t
example (f : Form) : (formulaGraph f).expression.toPolynomial.totalDegree≤4 := formulaGraph_degree f
example : AnnotatedSyntaxGraphs.fixedBodies.map (fun f => (formulaGraph f).witnessCount)=
    [84,84,108,104,108,188,264] := fixedBodies_graph_counts
example : (formulaGraph (fEq 0 0)).witnessCount=8 := by
  rw [formulaGraph_witnessCount]
  decide

private def accepted (t : Tree) (out : Nat) (w : Fin (width t) → Nat) : Bool :=
  let x : Fin (1+width t) → Nat := Fin.addCases (fun _ : Fin 1 => out) w
  (List.finRange (system t).rowCount).all (fun i =>
    ((system t).row i).eval (natAssignment x ((program t).eval x))==0)

private def first : Tree := .fork (.atom 0) (.atom 1)
private def second : Tree := .fork (.atom 0) (.atom 2)
private def nested : Tree := .fork first (.atom 2)
private def firstWitness : Fin (width first) → Nat := ![9,1,0,2]
private def nestedWitness : Fin (width nested) → Nat :=
  assemble first (.atom 2) ![116,1,5,10] firstWitness Fin.elim0
-- The forged parent rows agree with the fake child output eight. The child's
-- retained rows still reject the certificate.
private def forgedNested : Fin (width nested) → Nat :=
  assemble first (.atom 2) ![96,1,4,9] ![8,1,0,2] Fin.elim0

#eval accepted (.atom 3) 10 Fin.elim0
#eval !(accepted (.atom 3) 9 Fin.elim0)
#eval accepted first 9 firstWitness
#eval accepted second 28 ![28,0,2,5]
#eval accepted nested 116 nestedWitness
#eval !(accepted nested 96 forgedNested)
#eval !(accepted nested 117 nestedWitness)

#print axioms width
#print axioms width_eq
#print axioms assemble
#print axioms rootExpression
#print axioms rootExpression_eval
#print axioms rootExpression_degree
#print axioms localResiduals
#print axioms AnnotatedSharedSyntax.residual
#print axioms valid_fork_iff
#print axioms rootValue_sound
#print axioms valid_exists
#print axioms residual_degree
#print axioms equations
#print axioms equations_degree
#print axioms system
#print axioms holds_iff
#print axioms holds_split
#print axioms representation
#print axioms graph
#print axioms graph_witnessCount
#print axioms graph_degree
#print axioms system_rowCount
#print axioms formulaGraph
#print axioms formulaGraph_witnessCount
#print axioms formulaGraph_degree
#print axioms fixedBodies_graph_counts
