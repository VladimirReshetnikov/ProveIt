# The structured program and ZF0

`ProgramZF0.lean` composes two checked developments. The actual 219-node
`Dag254.dag254` program, iterated from nextproof = 2 and all other registers
zero, halts whenever the actual `PSCCalibration.ZF0Ax` theory has a refutation.
Consequently non-halting of this structured program implies consistency of
ZF without Foundation or Choice, including ordinary Infinity and Power Set.

The composition uses `L2.program_halts_iff` and
`QuotientZF0.c254_of_zf0_refutation`. The former proves equivalence with the
original numerical calculus; the latter constructs a CP/GIC quotient model
from every relevant nonempty encoded-bundle model and invokes the corrected
completeness theorem. No extra model-comparison hypothesis is inserted.

The L2 proof covers the actual AX output stack and gate, all dispatch cases
including halting, root iteration, and the two initial enumerator candidates.
It does not identify this structured DAG with the differently shaped literal
`Prog254` tree. That path-semantics comparison and the binary runtime theorem
remain separate, as do effective Foundation/Choice reductions, the converse
model interpretation and an internal arithmetic consistency equivalence.
There is no new machine table or state-count claim.

The merged L2 sources, this composition and the umbrella were rebuilt serially
with Lean 4.32.0 against verified source-identical dependencies. Both AX
generators reproduce their delivered current source exactly on scratch copies.
Nine theorem axiom audits and three actual callers pass, using only the
standard `propext`, `Classical.choice` and `Quot.sound` axioms. The literal
bootstrap and the entire dependency closure were not rebuilt. See
`results/l2-program88-integration-verification.json`.
