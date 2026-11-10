# Sign17 MC digit-to-byte chunk identities

This source-only sixteen-stage attempt replays the audited exact-degree
provider, then proposes six small independent `decide +kernel` equalities
between little-endian base-`2^47` digit lists and base-256 byte lists. They
cover the distinct MC block patterns at indices 0, 118, 119, 123, 125 and
251; the final case has three radix digits and 18 bytes, the others eight
digits and 47 bytes. The selected radix digits use the actual symbolic radix.

The guard externally verifies each source byte list and selected/unselected
digit pattern against the corresponding slice of the pinned decompressed MC
snapshot, and checks the seed, gzip and raw hashes. These Python/filesystem
checks are provenance observations, not Lean file/gzip/hash theorems. The
proposed Lean equalities concern six finite lists only. Reconstructing all
blocks, proving the maskList run structure and composing to the whole current
port remain separate; no new checked theorem or full port binding is claimed.

Prior source/provider audit pins and resource guards remain unchanged. Author
no-Lean preflight exited 0. Runner SHA-256:
`56fc7304eb692e2a2044867f584369365a130a19f384e0ec30d3ac185dabf5ba`;
manifest SHA-256:
`7151efc03ad765ac4928dcbfa089bba55ec8402377a50b0503cc58cd7029e662`;
new source SHA-256:
`209035b83ccfd257ee6396b738438dac7df1e6e8265b457ed201ad56766fb749`;
generator SHA-256:
`9159615494ec3dd0e49b7f3588037927339c7bfd79c503cb2bbcd6989b44aca4`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mc-chunk-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-mc-chunk-terminal-independent/README.md) passed; the packet is frozen.
