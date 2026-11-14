# PA194 increment: six-step append-spare tail

`PA194IncrementTail.lean` proves the append-spare tail from the physical
increment routine. Starting in dense state 1 with arbitrary left tape half
`l` and right half zero, the pinned PA194 machine reaches dense state 7 in
exactly six literal steps, with left half still `l` and right half 13. The
proof checks the actual table rows and uses the all-model packed-step and
binary tape lemmas. It holds for arbitrary model `l`, including nonstandard
elements.

`PA194IncrementTailSentence.lean` expresses that equality using explicit
primitive-recursive-code terms, proves it in candidate classical PRA, and
transfers it to native iPRA. In the upstream increment decomposition this is
the append-one tail phase; the complete source instruction also needs the
prefix scan, return phases, and source-frame correspondence. This package does
not establish either machine-consistency direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-increment-tail.sh
```

The checker regenerates the pinned PA194 table, rebuilds the carry-file and
physical-step dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
