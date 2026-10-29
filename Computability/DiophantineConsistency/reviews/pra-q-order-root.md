# All Foundation Robinson Q axiom images in candidate PRA

`PRAQOrder.modelLtWitness` derives the exact additive-witness definition
of the represented order in every candidate-PRA equality model, using the
nonzero characterization, subtraction reconstruction and cancellation.
First-order completeness gives an actual derivation of the mapped Foundation
`qLtDef`; `PRA_proves_all_Q` combines it with the earlier non-order cases
to derive the image of every actual Foundation `RobinsonQ` axiom. This is
axiom-wise compatibility. It is not yet an object translating arbitrary Q
proofs, an equivalence with standard PRA, or Parsons conservation.

The independent replay `/tmp/pra-q-order-root-eehniwj0` passed both modules
without warnings and matched the author object hashes; all three axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Its
driver checks current source and object hashes for the refreshed four-module
order provider and uses the independently replayed reconstruction and
subtraction-law providers. Foundation, Mathlib, PRATheory and the earlier
code providers remain inherited cache boundaries. The
[evidence packet](pra-q-order-root-replay/) preserves all author attempts,
including explicit `sorry` probes in attempts 3 and 4; neither is used in
the final source or successful replay.
