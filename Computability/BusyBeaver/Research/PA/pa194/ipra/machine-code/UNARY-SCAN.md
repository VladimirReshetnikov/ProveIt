# PA194 unary scanner in arbitrary PRA models

`PA194UnaryRuns.lean` constructs a finite primitive-recursive `ones` code and
proves its defining equations in every candidate classical PRA model. It also
binds the encoded PA194 state-1 transition to moving a single leading one.
`PA194ScanInvariant.lean` proves by quantifier-free open induction that, at
every time `k ≤ n`, the actual packed PA194 iterator has moved exactly `k`
of the `n` leading ones from the right tape half to the left. The quantified
model length, time, and tape halves may be nonstandard. The full-scan
corollary transfers all `n` bits in exactly `n` physical steps while keeping
state 1 (native state 0).

`PRA_proves_fullScanSentence` expresses the full-scan equality as a closed
first-order sentence and derives it in the candidate classical PRA, using
completeness over equality models. This proves one scanner segment, not the
entire register-box operation, source-to-machine simulation, or either
machine-specific iPRA consistency direction.

Replay with the documented overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-unary-scan.sh
```

The script regenerates the pinned table and rebuilds its dependency chain in
a private directory; it rejects `sorryAx`. The remaining transitive prebuilt
overlay objects are assumed to match their recorded sources.
