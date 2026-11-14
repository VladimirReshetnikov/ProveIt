# PA194 state-16 leftward one scanner

Dense state 16 in the pinned PA194 table reads and writes one, moves left,
and stays in state 16. `PA194StateSixteen.lean` and
`PA194SixteenTransition.lean` prove the exact physical and packed one-step
transition over arbitrary candidate classical PRA models.

`PA194SixteenScanInvariant.lean` proves by open induction that, starting
with left half `ones(n,l)` and right half `2*r+1`, after `k ≤ n` physical
steps the machine remains in state 16 with halves `ones(n-k,l)` and
`ones(k+1,r)`. The full-scan theorem covers arbitrary model elements,
including nonstandard lengths and tape halves.

The closed full-scan equality is proved in candidate classical PRA, and
`PA194SixteenNative.scan` transfers it to native iPRA. This proves a local
physical segment, not a full source-level instruction simulation or either
machine-consistency direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-sixteen-scan.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segment and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
