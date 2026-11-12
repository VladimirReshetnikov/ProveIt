# Proposed difference-ring proof for the 38-variable quartic

This packet supplies an **unelaborated proof draft** of the explicit
`EvaluationCut` in the separate [conditional model-transfer packet](../adaptive-qm38-conditional-model-draft/README.md).
The exact source files and `#print axioms` commands have not been run in Lean;
no model equivalence, endpoint proof, axiom closure or resource success is
claimed here.

`AdaptiveQM38Residuals.lean.src` copies the corrected 38-variable graph and
names the 29 residuals retained from the parent 40-variable sum of squares.
Its proposed `sum_eq_literal` is `rfl`. The generator and read-only checker
independently reconstruct the graph DAG externally and check that the child's
literal output is **syntactically** the ordered sum of those 29 named squares.
This external check supports the proposed `rfl`; it is not Lean reduction.

`AdaptiveQM38ResidualEvaluation.lean.src` proposes 29 individually named
identities in the difference ring, one for each matching parent/child residual
after extending the 38-vector by the two removed product values. Two more
identities assert that parent residuals 20 and 24 vanish under that extension.
The proposed `evaluation_identity` rewrites both literals to their ordered
sums, substitutes the 31 identities, and removes the two zero squares. It is
stated for arbitrary integer port values. `evaluation_cut` then specializes it
to the same `CurrentWindowCarry2011.ports` used by the historical 40-variable
endpoint. The separate conditional packet explains how this cut, the parent
residual slot recovery and the positivity maps would yield the no-zero
transport. Neither this packet nor that one is a direct natural-79 compact-port
reduction.

The source checker pins the corrected 38 graph and parent literal source,
checks the 29-to-31 index mapping and theorem statements, verifies that all
29 named child residuals are retained in order, and reconstructs the child's
sum DAG. The [candidate's external exact residual checker](../adaptive-square-sums38-two-quadratic-products/result.json)
also reproduces its 29 retained residual identities. These calculations do not
show that any of the Lean `simp`, `ring`, `rw`, definitional-equality or
`#print axioms` commands execute successfully. The 29 individual proofs may
need further splitting or resources; no runtime bound is established. Parent
provider provenance, all-model proof compilation and a connection to any
physical PDF remain separate.

From the repository root, reproduce the read-only source receipt:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-qm38-residual-evaluation-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/adaptive-qm38-residual-evaluation-draft/source-result.json
```

`generate.py` regenerates only the two inert source files in this packet and
prints the separate `result.json` observation. It does not invoke Lean or
materialize a build tree.
