# Sign17 symbolic MF source port versus compact byte-list decoding

This twenty-three-stage source-only attempt replays the independently audited
MF radix digits and concrete block composition. The new source proposes to
prove the actual symbolic 2012-digit list equals the flattened digit blocks,
then concludes `highPort + beta = Nat.ofDigits 256 mfBytesLE` and casts that
equality to exactly `CurrentWindowCarry2011.ports 3`. `mfBytesLE` is an
explicit finite list in Lean, compactly assembled from the ten audited block
fixtures. The separate [external block-layout review](../nine-sharing-sign17-mf-block-layout/README.md)
matched the same layout to the raw MF_source snapshot.

The external match is not a Lean statement about filesystem, gzip or hashes;
no JSON/PDF or full four-port binding is claimed. Provider source/state/outer/
audit pins and resource guards are retained. Author no-Lean preflight exited
0. Runner SHA-256:
`c1cf4fd0509569c98fc6679aa3804011434d7bac1287fea56dbb48f3d8167309`;
manifest SHA-256:
`078058a4a9e4a096d393a105bf37b9614e8335ec640c84f80723cdc5dafcf2ed`;
new source SHA-256:
`2e7f3e7a8ac607ebe603906697a30767a137623b145d95a9897764c6b2e662d9`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mf-whole-bytes-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-mf-whole-bytes-terminal-independent/README.md) passed; the packet is frozen.
