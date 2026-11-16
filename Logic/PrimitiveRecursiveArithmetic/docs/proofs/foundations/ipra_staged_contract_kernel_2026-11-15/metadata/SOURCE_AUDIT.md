# Source audit

Pinned ProveIt commit:

`38e83bc0d09647a98ce9fe5edf45d6b34f820dff`

Primary checked interfaces inspected:

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`

Repository status files inspected:

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`

Principal predecessor frameworks inspected:

- `foundations/ipra_embedding_framework`
- `foundations/ipra_framework`
- `foundations/ipra_finitary_interface_compiler_2026-11-15`
- `foundations/ipra_kernel_finite_use_framework_2026-11-15`
- `foundations/ipra_coherent_methods_2026-11-15`
- `foundations/ipra_resources_and_elimination_2026-11-15`
- `foundations/ipra_proof_carrying_observation_graphs_2026-11-15`
- `foundations/ocipra_framework_2026-11-15`

Audit conclusion: the packets strongly converge on finite contracts, reverse
demand, bounded traces, relational viability, and stable observations. Their
common unresolved engineering boundary is a compiled main theorem of type
`Prf PRAAx`. The present package focuses on the arity/context normalization
needed to make local object proofs composable by the already checked structural
rules.
