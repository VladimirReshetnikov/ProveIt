# PA194 connected scans through state 16

This extends `FIFTEEN-EXTENDED.md` by two literal physical steps. With an
odd initial left half `2*l+1`, the extended return reaches state 15 with
left half `2*l+1` and right half `2*u`, where
`u = zeros(n, zeros(m,1+4*r))`. The next step moves left onto the one, and
the following state-15 transition reads it and enters dense state 16.

From the state-12 configuration with left half `2*l+1` and right half
`zeros(n, 2*ones(m+1,2*r)+1)`, after exactly
`(((((((n+1)+(m+1))+1)+1)+m)+n)+1)+1` steps, the machine is in state 16
with left half `half(l)` and right half `parity(l)+2+8*u`. The result holds
for all elements of candidate classical PRA models, including nonstandard
lengths and tape halves.

`PA194FifteenExitSentence.lean` proves the corresponding universally closed
primitive-recursive-code equality in candidate classical PRA and transfers
it to native iPRA. This is a connected physical-machine segment, not a full
source-level instruction simulation or a machine-consistency reduction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-fifteen-exit.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segments and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
