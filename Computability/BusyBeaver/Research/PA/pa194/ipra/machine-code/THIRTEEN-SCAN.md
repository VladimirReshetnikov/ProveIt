# PA194 rightward one-erasing scanner

Dense state 13 in the pinned PA194 table reads one, writes zero, moves right,
and stays in state 13. Its exact physical and packed transitions are proved
in `PA194StateThirteen.lean` and `PA194ThirteenTransition.lean` over all
candidate classical PRA models.

`PA194ThirteenScanInvariant.lean` uses open induction to show that, from a
right half `ones(n,r)`, after `k ≤ n` physical steps the machine remains in
state 13 with left half `zeros(k,l)` and right half `ones(n-k,r)`. The
full-scan result holds for arbitrary model elements, including nonstandard
lengths. It connects naturally to the state-12 exit documented in
`TWELVE-EXIT.md`.

The closed full-scan equality is proved in candidate classical PRA, and
`PA194ThirteenNative.scan` transfers it to native iPRA. This proves a local
segment, not a full source-instruction simulation or either direction of a
machine-consistency equivalence.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-thirteen-scan.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segment and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
