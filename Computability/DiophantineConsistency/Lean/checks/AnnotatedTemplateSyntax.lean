import DiophantineConsistency.AnnotatedTemplateSyntax

open DiophantineConsistency AnnotatedTemplateSyntax

example {n : Nat} (t : Template n) (x : Fin n → Nat) (w : Fin (width t) → Nat) (h : Valid t x w) :
    rootValue t x w=value t x := rootValue_sound t x w h
example {n : Nat} (t : Template n) :
    (graph t).witnessCount=atomPortCount t+4*forkCount t := graph_witnessCount t
example {n : Nat} (t : Template n) :
    (graph t).expression.toPolynomial.totalDegree≤4 := graph_degree t
example {n : Nat} (t : Template n) :
    (system t).rowCount=atomPortCount t+4*forkCount t+1 := system_rowCount t
example {n : Nat} (t : Template n) (x : Fin n → Nat) :
    ∃ w : Fin (width t) → Nat,Valid t x w := valid_exists t x

private def accepted {n : Nat} (t : Template n) (x : Fin n → Nat) (out : Nat)
    (w : Fin (width t) → Nat) : Bool :=
  let visible : Fin (1+n) → Nat := Fin.addCases (fun _ : Fin 1 => out) x
  let assignment : Fin ((1+n)+width t) → Nat := Fin.addCases visible w
  (List.finRange (system t).rowCount).all (fun i =>
    ((system t).row i).eval (natAssignment assignment ((program t).eval assignment))==0)

private def raw : Template 1 := .port 0
private def atom : Template 1 := .atomPort 0
private def mixed : Template 2 := .fork (.atomPort 0) (.port 1)
private def correctMixed : Fin (width mixed) → Nat :=
  assemble (.atomPort 0) (.port 1) ![135,1,9,11] (fun _ => 10) Fin.elim0
private def forgedMixed : Fin (width mixed) → Nat :=
  assemble (.atomPort 0) (.port 1) ![93,1,7,9] (fun _ => 8) Fin.elim0

-- Raw ports carry values without a grammar assertion, including zero.
#eval accepted raw ![0] 0 Fin.elim0
#eval accepted atom ![3] 10 (fun _ => 10)
#eval !(accepted atom ![4] 10 (fun _ => 10))
#eval !(accepted atom ![3] 9 (fun _ => 10))
#eval accepted mixed ![3,2] 135 correctMixed
#eval !(accepted mixed ![3,2] 93 forgedMixed)
#eval !(accepted mixed ![3,2] 136 correctMixed)

#print axioms Template
#print axioms value
#print axioms width
#print axioms width_eq
#print axioms atomIndex
#print axioms rootExpression
#print axioms rootExpression_eval
#print axioms rootExpression_degree
#print axioms residual
#print axioms valid_fork_iff
#print axioms rootValue_sound
#print axioms valid_exists
#print axioms residual_degree
#print axioms equations
#print axioms equations_degree
#print axioms holds_split
#print axioms representation
#print axioms graph
#print axioms graph_witnessCount
#print axioms graph_degree
#print axioms system_rowCount
