import DiophantineConsistency.AnnotatedRefutationPR

/-! # Exact supplied program-tree counts for the direct sealed-ZFC checker

These are source-code tree counts, not polynomial variable counts. The proof
reduces only finite program syntax and never constructs a graph representation
or evaluates a large fixed formula-code numeral.
-/
namespace DiophantineConsistency.AnnotatedCheckerSize
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

theorem axiomDispatch_nodeCount :
    AnnotatedAxiomDispatch.P.program.val.nodeCount=58007 := by decide

theorem optimizedAxiomDispatch_nodeCount :
    AnnotatedAxiomDispatch.optimizedProgram.val.nodeCount=52913 := by decide

theorem axiomContext_nodeCount :
    AnnotatedAxiomContext.P.program.val.nodeCount=58281 := by decide

theorem optimizedAxiomContext_nodeCount :
    AnnotatedAxiomContext.optimizedProgram.val.nodeCount=53187 := by decide

theorem refutation_nodeCount :
    AnnotatedRefutationPR.refutationProgram.val.nodeCount=83281 := by decide

theorem optimizedRefutation_nodeCount :
    AnnotatedRefutationPR.optimizedProgram.val.nodeCount=76313 := by decide

end DiophantineConsistency.AnnotatedCheckerSize
