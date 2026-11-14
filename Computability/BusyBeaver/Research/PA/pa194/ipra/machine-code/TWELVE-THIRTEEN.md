# PA194 connected state-12 and state-13 scans

`PA194TwelveThirteenCompose.modelTwoScans` composes two adjacent literal
engine segments using the all-model stepper composition theorem. It starts
in dense state 12 with left half `l` and right half
`zeros(n, 2*ones(m,r)+1)`. The machine scans `n` zero bits to the right,
consumes the next one while entering state 13, then scans `m` one bits to
the right while writing zeros. After exactly `(n+1)+m` physical steps it is
in state 13 with left half `zeros(m, 2*zeros(n,l))` and right half `r`.

The proof covers arbitrary elements of each candidate classical PRA model,
including nonstandard values of both lengths and tape halves.
`PA194TwelveThirteenSentence.lean` states the four-variable result as a
universally closed primitive-recursive-code equality, proves it in candidate
classical PRA by completeness, and transfers it to native iPRA.

This is a connected physical-machine segment, not a complete source-level
instruction simulation or either direction of the machine-consistency
equivalence.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-twelve-thirteen.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segments and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
