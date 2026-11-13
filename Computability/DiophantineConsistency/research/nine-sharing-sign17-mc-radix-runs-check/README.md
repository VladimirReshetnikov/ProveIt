# Sign17 symbolic MC radix-digit runs

This sixteen-stage source-only attempt replays the audited symbolic provider
and proposes to prove that the actual low mask's 2011 base-`2^47` digits are
six alternating runs of lengths 951, 9, 26, 18, 1 and 1006, starting with
`radix−2` and alternating with `radix−1`. It uses list extensionality and the
already checked `LowMaskCoding.ofDigits_maskList` theorem to avoid the
whole-mask kernel computation that overflowed the stack. The resulting
proposed theorem refers to the actual symbolic lowPort only.

No new theorem is claimed yet; byte-chunk composition, full literal equality,
and Lean statements about gzip/JSON/files remain separate. Prior provider and
resource guards are retained. Author no-Lean preflight exited 0. Runner
SHA-256:
`e5835d39277d0049a384e6135fefa8d3dcb6633ea29ad8b9d50e4bfaac184394`;
manifest SHA-256:
`fcf611a47b5689049d80c20f8ac0a08686c6b2b0f3013e06aa02ecb3b6787a6c`;
new source SHA-256:
`bd70e53dbd6f0fc6617e30c142cf6f7188b98cc9bc40d38812a846c1a7fc07cf`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mc-radix-runs-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-mc-radix-runs-terminal-independent/README.md) passed; the packet is frozen.
