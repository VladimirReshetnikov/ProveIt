# PA194 connected run through the state-16 scanner

This extends `FIFTEEN-EXIT.md` through the state-16 leftward one scanner in
`SIXTEEN-SCAN.md`. Let `v = ones(p,l)` and
`u = zeros(n, zeros(m,1+4*r))`. Start in dense state 12 with left half
`2*(2*v+1)+1` and right half `zeros(n, 2*ones(m+1,2*r)+1)`. After
`(((((((n+1)+(m+1))+1)+1)+m)+n)+1)+1)+p` literal steps, the machine is in
state 16 with left half `l` and right half `ones(p+1,1+4*u)`.

`PA194SixteenConnected.modelConnectedSixteen` proves the complete connected
segment over arbitrary candidate classical PRA models; `n`, `m`, `p`, `l`,
and `r` may all be nonstandard. `PA194SixteenConnectedSentence.lean`
expresses the result as a universally closed primitive-recursive-code
equality, proves it in candidate classical PRA, and transfers it to native
iPRA.

This is a connected physical-machine segment. It is not yet a full
source-level instruction simulation or a machine-consistency reduction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-sixteen-connected.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segments and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
