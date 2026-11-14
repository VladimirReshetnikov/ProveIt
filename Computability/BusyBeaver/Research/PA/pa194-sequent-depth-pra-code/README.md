# Candidate-PRA code for PA194 sequent depth

`numericSequentDepth` decodes a natural number as a list of numeric source
formula codes and evaluates the primitive-recursive sequent-depth function.
It is total, with an empty-list default for invalid list codes, and is proved
primitive recursive.

`sequentDepth_code_correct` gives an existential finite candidate-PRA `Code 1`
whose standard natural-number evaluation on the code of an actual source
sequent is the exact `sequentDepth` used as a node annotation by the list LK
budget evaluator.

Both theorems checked in the ordered source overlay against freshly rebuilt
candidate-PRA code objects, reporting `[propext, Classical.choice, Quot.sound]`
and no `sorryAx`. The full nested standalone script remains untested.

The code witness is existential and the equation holds in the standard
natural-number evaluation. Extraction of an annotated budget tree from coded
Foundation proofs, correctness in arbitrary candidate-PRA models, and the
PA194 machine calibration remain open.

To rebuild from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited current Foundation object overlay and run
`bash Computability/BusyBeaver/Research/PA/pa194-sequent-depth-pra-code/check.sh`.
