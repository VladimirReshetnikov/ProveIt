# PA194 connected scans through the state-14 exit

This extends `TWELVE-THIRTEEN.md` by one literal machine step. Dense state
13 reads a zero, writes zero, moves left, and enters dense state 14. The
transition is proved in `PA194StateThirteenExit.lean` and composed with the
preceding zero and one scans in `PA194ThirteenExitComposition.lean`.

Starting in state 12 with left half `l` and right half
`zeros(n, 2*ones(m,2*r)+1)`, let `z = zeros(m, 2*zeros(n,l))`. After
exactly `((n+1)+m)+1` physical steps the machine is in state 14, with left
half `half(z)` and right half `parity(z) + 4*r`. This holds in every
candidate classical PRA model for arbitrary elements `n`, `m`, `l`, and
`r`, including nonstandard values.

`PA194ThirteenExitSentence.lean` proves the corresponding universally closed
primitive-recursive-code equality in candidate classical PRA and transfers
it to native iPRA. The result is a connected physical-machine segment; it is
not a full source-level instruction simulation or a machine-consistency
reduction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-thirteen-exit.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segments and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
