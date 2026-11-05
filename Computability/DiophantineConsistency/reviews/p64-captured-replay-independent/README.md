# Independent review of the P64 captured-provider replay

The retained records support the reported **eight-module captured-provider
replay**, subject to its stated import-shim and ancestry limits. This
review did not invoke Lean or independently observe the original process.

The read-only check below confirmed the eight-module order and recorded
zero exits; matching hashes for all eight canonical sources, temporary
build sources, fresh output objects and copied logs; and the absence of
the recorded warning/error/`sorryAx` strings. It independently enumerated
the 17 direct `import` lines in the build sources, checked their recorded
first existing paths and hashes in the stated search order, and checked
that imports of earlier selected P64 modules point to those fresh objects.
The nine retained external direct-provider guard hashes and the Lean
binary hash also match the current files.

Seven temporary build sources are byte-for-byte the canonical sources.
For `P64Graph`, the build source replaces the first
`FreeJSumSquares` import with `P65GraphShim`; the remainder is identical.
Thus this is a replay with an explicit import substitution, not a clean
rebuild of the unmodified source closure. The shim object and other
inherited providers remain captured inputs; their full source, package,
dynamic-load and temporal ancestry was not authenticated here.

The retained endpoint log reports `positiveBridge`,
`native_equivalence`, `standard_equivalence`, and `reference_equivalence`
with `[propext, Classical.choice, Quot.sound]`. The retained terminal
observation reports outer session 91344 exit 0 and cites the exact runner,
records, result, and read-only-audit hashes verified here. That is an
observation record, not an independently witnessed replay by this review.
The endpoint is for the Lean expression and selected mapped consistency
sentence; exact JSON, compressed payload, and rendered-page bindings retain
the separate limits described in the [replay packet](../../research/fourteen-p64-independent-replay/README.md).

## Reproduction

The following read-only command exited 0 and wrote the captured
[`result.json`](result.json). It requires the still-available temporary
providers named by the replay and does not execute Lean.

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-captured-replay-independent/review.py
```

```text
edc1f6deaf788c34f55bf13e7c834e8cd3002b3dd0aa9baa7be00ce708cd6c5d  review.py
75634680b7538380b774903083c142e84f5944c7723653356e18b312538ebfe6  result.json
```
