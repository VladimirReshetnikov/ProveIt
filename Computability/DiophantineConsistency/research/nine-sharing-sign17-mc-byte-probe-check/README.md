# Sign17 MC byte literal: bounded kernel probe

This source-only sixteen-stage attempt replays the audited symbolic exact
provider, then asks Lean to prove `CurrentMasks2011.lowPort = mcLiteral` and
that the integer cast is exactly `CurrentWindowCarry2011.ports 2`. The
literal has 23,630 hexadecimal digits generated from the pinned 11,815-byte MC
snapshot. The candidate proof unfolds the actual symbolic low mask, rewrites
its finite support, and asks for `decide +kernel`; it is a bounded feasibility
probe and may run out of time or memory. It sets local recursion depth 100000
and heartbeats 4000000; the existing 120-second child limit, 4-GiB sampled RSS
limit, 10-GiB host-available floor, and Lean `-M3600` guard are retained.

The preflight guard externally checks the seed hash, gzip hash, decompressed
raw hash/length and exact source hex bytes. These Python/filesystem checks are
provenance observations, not a Lean theorem about gzip, hash or files. The
proposed Lean theorem concerns the numerical literal, if it compiles; no
result or full JSON/PDF binding is claimed yet. A separate independently
reviewed external MC/MF numerical recomputation is documented in
[the binding design](../nine-sharing-sign17-external-binding-design/README.md).

Author no-Lean preflight exited 0. Runner SHA-256:
`824b8a2735f9c73d4c93192e781c45c4a9a0f48a90a2f59d8321fc937198d635`;
manifest SHA-256:
`d7365879a11067aedda46ceb72c0ff8334575cb45f5913487943ac63bf0408a9`;
new source SHA-256:
`de14ab2a18d560eb71022a5dc518129bc596206c6827c07789760e2b579ea4c6`;
generator SHA-256:
`2735f3937b805c586750a0216f09ed12acd04ec66ae5cfb0ccbca9ac25abd80a`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mc-byte-probe-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-mc-byte-probe-terminal-independent/README.md) passed; the packet is frozen.
