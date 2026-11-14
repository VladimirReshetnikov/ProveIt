# PA194 increment: carry across a fixed register file

This package proves the carry-file phase following the selected marked-cell
phase in `SELECTED-CELL.md`. At dense state 1, one regular register block
`0 1^(v+1)` is crossed in exactly `2+v` physical steps: the machine writes
`10` in place of the first two crossed bits, scans the remaining `v` ones,
and stays in dense state 1. Two pinned PA194 table rows and the previously
proved variable-length one scanner establish this in every candidate
classical PRA model.

`PA194CarryFile.lean` composes that segment across any fixed standard number
of register blocks. It explicitly constructs primitive-recursive function
codes for the total clock and resulting left tape, and proves the complete
physical run preserves the arbitrary suffix. The register values, input left
half, and suffix may all be nonstandard model elements. The corresponding
universally closed fixed-arity equality is proved in native iPRA by
`PA194CarryFileSentence.lean`.

This is the carry-file phase of the increment operation, not yet the complete
source instruction: the prefix scan, append-spare, and return phases and their
source-frame composition remain separate. It does not establish either
machine-consistency direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-carry-file.sh
```

The checker regenerates the pinned PA194 table, rebuilds the marked-file and
physical-run dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
