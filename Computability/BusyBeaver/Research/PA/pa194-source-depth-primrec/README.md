# Primitive-recursive PA194 formula and sequent depth

`depthCode` is a total numerical function and `depthCode_primrec` proves it
primitive recursive using a primitive-recursive table step and
`Primrec.nat_strong_rec`. `depthCode_correct` identifies its value on the
Foundation code of every PA194 source formula with the exact source `depth`.

`sequentDepthCode` takes a list of natural-number formula codes and folds their
depths with `max`. Lean proves it primitive recursive, and
`sequentDepthCode_correct` identifies it with the exact `sequentDepth` of the
corresponding Foundation sequent. That quantity appears in every node of the
actual list-based Foundation LK compiler's `listFoundationBudget`.

The six printed theorems pass the ordered local overlay check and report
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The nested
standalone script has not yet been replayed.

Correctness is asserted on genuine source formula codes. This does not yet
encode LK derivation trees, prove `listFoundationBudget` or the whole proof
compiler primitive recursive, internalize their correctness in arithmetic, or
prove a PA194 machine reduction.

To rebuild from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited current Foundation object overlay and run
`bash Computability/BusyBeaver/Research/PA/pa194-source-depth-primrec/check.sh`.
