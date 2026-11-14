# PA194 rightward zero scanner

Dense state 12 in the pinned PA194 table reads and writes zero, moves right,
and stays in state 12. `PA194StateTwelve.lean` and
`PA194TwelveTransition.lean` prove its exact physical and packed one-step
transition over arbitrary candidate classical PRA models.

`PA194TwelveScanInvariant.lean` uses open induction to prove a partial
progress invariant for an initial right half `zeros(n,r)`. After `k ≤ n`
physical steps the machine remains in state 12, the left half is
`zeros(k,l)`, and the right half is `zeros(n-k,r)`. The full-scan result
holds for arbitrary model values, including nonstandard lengths. `zeros`
is an explicit primitive-recursive code for adding low-order zero bits to a
binary tape half.

The closed full-scan equality is proved in candidate classical PRA, and
`PA194TwelveNative.scan` transfers it to native iPRA. This is a local
machine segment, not a full source-instruction simulation or either direction
of the desired consistency equivalence.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-twelve-scan.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segment and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the whole foundation and iPRA chain
is not rebuilt by this replay.
