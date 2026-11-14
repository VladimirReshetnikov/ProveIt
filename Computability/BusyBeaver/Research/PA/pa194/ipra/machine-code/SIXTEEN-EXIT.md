# PA194 connected scans through state 17

This extends `SIXTEEN-CONNECTED.md` through the zero boundary of the
state-16 leftward one scanner. Let

- `u = zeros(n, zeros(m,1+4*r))`,
- `v = ones(p,2*l)`, and
- `a = ones(p,1+4*u)`.

Start in dense state 12 with left half `2*(2*v+1)+1` and right half
`zeros(n, 2*ones(m+1,2*r)+1)`. After exactly
`((((((((((n+1)+(m+1))+1)+1)+m)+n)+1)+1)+p)+1)+1` literal steps the
machine is in state 17 with left half `half(l)` and right half
`parity(l)+4*(2*a+1)`.

The two final physical transitions are proved separately and composed with
the connected run in `PA194SixteenExitComposition.lean`. The result covers
arbitrary elements `n`, `m`, `p`, `l`, and `r` of candidate classical PRA
models, including nonstandard elements. `PA194SixteenExitSentence.lean`
proves the universally closed primitive-recursive-code equality in candidate
classical PRA and transfers it to native iPRA. This is a connected physical
segment, not a full source-level simulation or a machine-consistency
reduction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-sixteen-exit.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segments and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
