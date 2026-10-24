import DiophantineConsistency.AnnotatedCheckerSize

open DiophantineConsistency AnnotatedCheckerSize
example : AnnotatedAxiomDispatch.P.program.val.nodeCount=58007 := axiomDispatch_nodeCount
example : AnnotatedAxiomDispatch.optimizedProgram.val.nodeCount=52913 := optimizedAxiomDispatch_nodeCount
example : AnnotatedAxiomContext.P.program.val.nodeCount=58281 := axiomContext_nodeCount
example : AnnotatedAxiomContext.optimizedProgram.val.nodeCount=53187 := optimizedAxiomContext_nodeCount
example : AnnotatedRefutationPR.refutationProgram.val.nodeCount=83281 := refutation_nodeCount
example : AnnotatedRefutationPR.optimizedProgram.val.nodeCount=76313 := optimizedRefutation_nodeCount

#print axioms axiomDispatch_nodeCount
#print axioms optimizedAxiomDispatch_nodeCount
#print axioms axiomContext_nodeCount
#print axioms optimizedAxiomContext_nodeCount
#print axioms refutation_nodeCount
#print axioms optimizedRefutation_nodeCount
