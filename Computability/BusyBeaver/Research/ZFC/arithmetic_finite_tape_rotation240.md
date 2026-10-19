# Finite tape encodings in arithmetic models

[`ArithmeticFiniteTapeRotation240`](../../Lean/BusyBeaver/ZFC/ArithmeticFiniteTapeRotation240.lean)
identifies finite bit and register encodings with the numeric tape functions
used by the 240-state arithmetic simulation. Finite lists and repetition
counts are external natural data; every following tape suffix can be an
arbitrary element of an IΣ₁ model. The pairing and configuration adapters
transport numerals without unfolding the large startup configuration.

The [actual check](results/arithmetic-finite-tape-rotation240-verification.json)
passes eight axiom probes and ten typed callers, including the 167-spare
startup count, with zero warnings and only standard axioms. Source and audit
took 2.466 and 2.092 seconds at default proof limits, within a shared
120-second limit using one thread and 4,096 MiB. Existing checked providers
were reused without rebuilding their dependency families.

The [preserved history](arithmetic-finite-tape-rotation240/history.json.gz)
includes the failed first attempt: an invalid `omit` removed an instance
needed by the numeric prefix definition. Removing that declaration fixed
elaboration without changing any theorem statement or proof limit. The
[publication record](results/arithmetic-finite-tape-rotation240-publication.json)
binds the accepted source, audit, logs and provider records.

These are encoding identities, not machine execution theorems. They support
the remaining exact startup and instruction-frame identifications. Attribution
remains with Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt.
