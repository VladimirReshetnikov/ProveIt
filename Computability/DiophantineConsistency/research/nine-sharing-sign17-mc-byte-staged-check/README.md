# MC literal and proof: bounded split diagnostic

This fresh-output seventeen-stage diagnostic replays the audited symbolic
provider, then isolates the exact same 23,630-digit MC literal declaration and
reflexivity theorem from the original finite-mask equality proof. It asks
whether Lean can compile the literal alone before attempting the expensive
mask comparison in its own module. The intended equality statements and
proof are otherwise unchanged. A successful literal module alone says only
that the numeral elaborates; it is not a symbolic-port equality.

The [first MC attempt](../nine-sharing-sign17-mc-byte-probe-check/attempt01/README.md)
failed with a stack overflow and is independently audited. This diagnostic
retains the local recursion/heartbeat settings and the same -M3600, sampled
4-GiB RSS, 10-GiB available floor and 120-second child guard. It does not
assume or raise the native stack limit. The source literal is externally
checked against the pinned MC raw/gzip bytes; that remains external provenance,
not a Lean theorem about files. No new equality theorem is claimed yet.

Author no-Lean preflight exited 0. Runner SHA-256:
`1d499302c9b3550a66424d1e8597ed0aaf5f75eaa3880cfae5f87f66214f8801`;
manifest SHA-256:
`2930672c9b14ddaeac99fe2c91fc188e3661b0f721e7213fb3c65cbc760dc31a`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mc-byte-staged-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-mc-byte-staged-terminal-independent/README.md) passed; the packet is frozen.
