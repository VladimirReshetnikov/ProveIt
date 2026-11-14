# PA194 leftward one scanner

Dense state 6 in the pinned PA194 table reads and writes a one, moves left,
and stays in state 6. `PA194StateSix.lean` and `PA194SixTransition.lean`
prove the exact physical and packed one-step transition over arbitrary
candidate classical PRA models.

`PA194SixScanInvariant.lean` proves by open induction a partial-progress
invariant for an initial configuration with left half `ones(n,l)` and
right half `2*r+1`. After `k ≤ n` physical steps, the machine remains in
state 6 with halves `ones(n-k,l)` and `ones(k+1,r)`. Its full-scan corollary
covers arbitrary model values, including nonstandard scan lengths, and its
closed equality is provable in the candidate classical PRA. The local
`ones` constructor places the indicated number of low-order one bits onto a
binary half; the right-half hypothesis makes the initial read bit one.

`PA194SixNative.scan` transfers the closed full-scan equality to the native
iPRA `standardTheory`. This establishes one machine-specific segment. It
does not prove a complete source-instruction simulation or either direction
of the machine's consistency equivalence.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-six-scan.sh
```

The script regenerates the pinned PA194 table, rebuilds the scan and its
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the whole foundation and iPRA
chain is not rebuilt by this replay.
