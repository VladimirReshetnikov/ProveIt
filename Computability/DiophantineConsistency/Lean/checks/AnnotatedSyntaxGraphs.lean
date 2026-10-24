import DiophantineConsistency.AnnotatedSyntaxGraphs

open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency DiophantineConsistency
open AnnotatedProofCode AnnotatedRename AnnotatedSyntaxGraphs

example {out a b t s m : Nat} (h : ForkCertificate out a b t s m) :
    out=forkCode a b := forkCertificate_sound h
example {out a b : Nat} (h : out=forkCode a b) :
    ∃ t s m,ForkCertificate out a b t s m := forkCertificate_complete h
example : forkGraph.witnessCount=3 := forkGraph_witnessCount
example : forkGraph.expression.toPolynomial.totalDegree≤4 := forkGraph_degree
example (t : Tree) : (treeGraph t).witnessCount=5*forkCount t := treeGraph_witnessCount t
example (f : Form) : (formulaGraph f).witnessCount=5*forkCount (quoteForm f) := formulaGraph_witnessCount f
example : AnnotatedCodeGraphs.forkConstructor.witnessCount=forkGraph.witnessCount+5 := forkGraph_saves_five

#eval decide (ForkCertificate 3 0 0 1 1 1)
#eval decide (ForkCertificate 6 0 2 0 0 2)
#eval !(decide (ForkCertificate 0 0 0 1 1 1))
#eval !(decide (ForkCertificate 3 0 0 2 1 1))
#eval !(decide (ForkCertificate 3 0 0 1 0 1))
#eval (atomGraph 0).witnessCount==0
example : forkGraph.expression.binaryOps=54 := forkGraph_binaryOps
-- Count-only folds, not closed graph construction or formula-code evaluation.
example : fixedBodies.map (fun f => (formulaGraph f).witnessCount)=[105,105,135,130,135,235,330] :=
  fixedBodies_graph_counts

#print axioms ForkCertificate
#print axioms forkCertificate_iff
#print axioms forkCertificate_sound
#print axioms forkCertificate_complete
#print axioms rows
#print axioms system
#print axioms holds_iff
#print axioms representation
#print axioms forkGraph
#print axioms forkGraph_witnessCount
#print axioms forkGraph_degree
#print axioms atomGraph
#print axioms atomGraph_witnessCount
#print axioms forkCount
#print axioms treeGraph
#print axioms treeGraph_witnessCount
#print axioms formulaGraph
#print axioms formulaGraph_witnessCount
#print axioms forkGraph_saves_five

#print axioms forkGraph_binaryOps
#print axioms fixedBodies_graph_counts
