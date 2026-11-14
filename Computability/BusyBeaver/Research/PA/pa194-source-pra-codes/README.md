# Candidate-PRA function codes for PA194 source operations

The preceding packages establish standard-Lean primitive-recursiveness of
numeric source formula shift, formula depth, and the annotated-LK-tree budget
evaluator. Here the existing `PRAFiniteFunctionCodes.exists_code_of_primrec`
theorem supplies a finite candidate-PRA `Code 1` for each operation.

Three direct equations connect their standard natural-number evaluations to:

- Foundation's actual shift on every encoded PA194 source formula;
- the source `depth` on every such formula; and
- `listFoundationBudget` of every Foundation LK derivation, when the input is
  the code of its annotated budget tree.

The two candidate-PRA code source dependencies were freshly compiled in an
independent tmpfs overlay from the pinned repository sources. The bridge file
then checked against those fresh objects and the ordered source-side overlay.
Its printed theorems report `[propext, Classical.choice, Quot.sound]`, with no
`sorryAx`. The full nested standalone script has not yet been replayed.

These are existential standard-Lean results; no particular finite code trees
are printed. The annotated tree is not yet extracted by a proved
primitive-recursive function from an encoded Foundation derivation. In
particular these results do **not** prove the equations in arbitrary
candidate-PRA models, internalize the compiler in arithmetic, or establish the
PA194 machine calibration.

To rebuild from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited current Foundation object overlay and run
`bash Computability/BusyBeaver/Research/PA/pa194-source-pra-codes/check.sh`.
