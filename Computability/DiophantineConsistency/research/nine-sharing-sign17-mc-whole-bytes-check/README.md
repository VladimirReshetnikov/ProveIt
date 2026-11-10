# Sign17 symbolic MC port versus compact byte-list decoding

This twenty-one-stage source-only attempt replays the independently audited
radix-run and concrete block composition results. The new source proposes to
prove the six symbolic runs equal the concatenated digit blocks, then concludes
`CurrentMasks2011.lowPort = Nat.ofDigits 256 mcBytesLE` and casts that equality
to `CurrentWindowCarry2011.ports 2`. `mcBytesLE` is an explicit finite list in
Lean, compactly assembled from the six audited block fixtures.

The separate external block-layout review shows that the same fixture layout
reconstructs the reversed raw MC snapshot. That observation is not a Lean
statement about filesystem, gzip or hashes; no JSON/PDF or full four-port
binding is claimed. Provider source/state/outer/audit pins and resource guards
are retained. Author no-Lean preflight exited 0. Runner SHA-256:
`bf607efd726082e98ec61d2dd8b9c040c8a1098d0cdc360b28a1653f078e475a`;
manifest SHA-256:
`0cf514b35d053c84f4d81643c9086f9d11d630c2570186bd68cc8adb41e510d1`;
new source SHA-256:
`188a068af57bfb5df0be8dc56005dc76fec66dd10a626e1995f457bd74d62bc9`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mc-whole-bytes-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-mc-whole-bytes-terminal-independent/README.md) passed; the packet is frozen.
