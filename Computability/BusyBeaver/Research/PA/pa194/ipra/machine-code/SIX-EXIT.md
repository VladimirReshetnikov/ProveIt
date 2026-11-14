# PA194 scanner boundary and exit

This extends `SIX-SCAN.md` through the first zero after a leftward run of
ones. The exact dense-state-6 transitions in `PA194StateSixBoundary.lean`
and `PA194StateSixExit.lean` prove, over every candidate classical PRA
model, the one-reading transition that moves onto a zero and the subsequent
zero-reading transition into dense state 7. Their packed versions are composed
with the variable-length scanner in `PA194SixBoundaryComposition.lean`.

Starting in state 6 with left half `ones(n, 2*l)` and right half `2*r+1`,
the machine reaches state 7 after exactly `n+2` physical steps. Its final
left half is `half(l)`; its final right half is `parity(l) + 4*a`, where
`a = ones(n+1,r)`. The theorem holds for arbitrary elements of each
candidate PRA model, including nonstandard `n`, `l`, and `r`. Here `half`
and `parity` are the explicitly encoded binary tape functions.

`PA194SixExitSentence.lean` expresses this composition as a universally
closed equality of explicit primitive-recursive-code terms, proves it in
candidate classical PRA by completeness over equality models, and transfers
it to native iPRA. It proves a local machine segment, not the entire
source-instruction simulation or either machine-consistency direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-six-exit.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segment and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
