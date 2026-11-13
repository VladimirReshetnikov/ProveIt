# Sign17 MF source-port digit-to-byte chunks

This source-only sixteen-stage attempt replays the audited symbolic provider,
then proposes ten small kernel equalities between little-endian radix-`2^47`
digit lists and base-256 byte lists at representative MF_source block indices
0, 1, 114, 115, 120, 121, 123, 124, 125 and 251. The last case has four
radix digits and 18 bytes; all others have eight digits and 47 bytes.

The guard externally checks the seed and gzip/raw hashes and verifies each
source fixture against the pinned MF raw snapshot and manually transcribed
radix-digit pattern. This is external provenance, not a Lean theorem about
files/gzip/hash. The separate independently audited block-layout reconstruction
is [here](../nine-sharing-sign17-mf-block-layout/README.md). No new checked
chunk, whole-port, JSON or PDF theorem is claimed yet.

Author no-Lean preflight exited 0; resource limits are unchanged. Runner
SHA-256:
`8c493f1bf76a3680bcf351b76a80391d4181988f7a028f5f39ddcf8857e900a7`;
manifest SHA-256:
`42c674944f2e491f86152a218bd64e1bb8c183e26de95656c96fd69f30df5768`;
new source SHA-256:
`f7aa7519057ef3d63140210efb997bf601bdbcd6be7b6626044684c538818192`;
generator SHA-256:
`3559a979fd695fdf13d2250966b2efe4078e9c5e73bb1ac0b47dbd4539b2d6b1`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mf-chunk-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-mf-chunk-terminal-independent/README.md) passed; the packet is frozen.
