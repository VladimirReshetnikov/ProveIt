# PA194 rightward zero scanner exit

This extends `TWELVE-SCAN.md` by consuming the first one after a rightward
run of zeros. The actual dense-state-12 transition on that one writes zero,
moves right, and enters dense state 13. The formalization composes this
transition with the variable-length scanner in every candidate classical PRA
model.

Starting in state 12 with left half `l` and right half `zeros(n, 2*r+1)`,
the machine reaches state 13 after exactly `n+1` physical steps. Its final
left half is `2*zeros(n,l)` and its final right half is `r`. The theorem
covers arbitrary model elements, including nonstandard scan lengths and
tape halves.

`PA194TwelveExitSentence.lean` expresses this as a universally closed
primitive-recursive-code equality, proves it in candidate classical PRA by
completeness over equality models, and transfers it to native iPRA. This
proves a local segment, not a complete source-instruction simulation or
either machine-consistency direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-twelve-exit.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segment and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
