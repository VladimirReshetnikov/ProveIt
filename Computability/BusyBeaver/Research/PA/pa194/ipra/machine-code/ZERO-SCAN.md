# PA194 leftward zero scanner in arbitrary PRA models

`PA194StateFifteen.lean` proves the actual dense-state-15/native-state-1
zero-reading left move in every candidate classical PRA model, including for
nonstandard tape values. `PA194ZeroRuns.lean` defines a primitive-recursive
code for extending a binary tape half by a model-length block of zeros.
`PA194ZeroScanInvariant.lean` proves that at each `k ≤ n` the packed machine
iterator has moved k zeros from the left half to the right. Its full-scan
corollary proves that n zeros are moved in exactly n physical steps, for all
model lengths and tape halves, including nonstandard elements.

`PRA_proves_fullScanSentence` packages that full-scan equality as a closed
first-order sentence and derives it in the candidate classical PRA by
completeness over equality models. This is one register-engine scanner, not
the complete register-box operation, source-to-machine simulation, or a
machine-specific iPRA consistency direction.

Replay using the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-zero-scan.sh
```

The checker regenerates the pinned table and rebuilds the dependency chain in
a private directory; it rejects `sorryAx`. Transitive prebuilt overlay objects
are assumed to match the recorded sources, not all rebuilt by this replay.
