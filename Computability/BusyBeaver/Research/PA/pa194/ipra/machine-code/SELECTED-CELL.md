# PA194 increment: selected marked-register phase

This package proves one physical phase of the PA194 increment operation.
The pinned PA194 dense state 2 corresponds to native control 64. Starting
there with a marked first register `00 1^v`, an arbitrary left half `l`,
and an arbitrary right suffix `t`, the literal machine consumes the two
zeros and scans the `v` ones. After exactly `2+v` steps it is in dense state
1, with right half `t` and left half `ones(v,4*l+1)`.

`PA194SelectedCell.lean` proves the phase for arbitrary candidate classical
PRA model elements, including nonstandard `v`, `l`, and `t`.
`PA194MarkedFile.lean` packages the same transition for an arbitrary fixed
number of subsequent register blocks and an arbitrary numeric suffix. Its
marked block and file are explicit primitive-recursive function codes.
`PA194MarkedFileStandard.lean` proves that, on natural-number register
lists, this code matches the actual imported `M6.Runtime.sepsM 0` marked-file
layout. Both the raw selected-cell equality and the fixed-arity marked-file
equality are proved in native iPRA via their corresponding sentence modules.

This is the selected-cell subphase, not a complete source increment
instruction: the prefix scan, carry, append-spare, and return phases still
need to be combined with source frames. It does not establish either
machine-consistency direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-selected-cell.sh
```

The checker regenerates the pinned PA194 table, rebuilds the marked-file and
physical-run dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
