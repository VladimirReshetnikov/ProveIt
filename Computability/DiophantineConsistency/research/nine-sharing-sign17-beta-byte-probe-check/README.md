# Sign17 symbolic beta byte-pattern probe

This sixteen-stage source-only attempt replays the audited exact-degree
provider, then proposes a kernel theorem that the big-endian digit list
`31 :: replicate 11814 255` decodes to `CurrentMasks2011.beta` and to exactly
`CurrentWindowCarry2011.ports 0`. The proposed proof uses a general repunit
identity and symbolic exponent algebra; it does not claim that Lean has read,
decompressed, hashed or parsed any external file. The distinct [external
beta-byte check](../nine-sharing-sign17-external-binding-design/README.md)
observes that the frozen gzip snapshot decodes to the same pattern, using
Python. No connection between that observation and Lean beyond the stated
shared pattern is yet kernel-checked, and the other three ports, JSON and PDF
remain unbound.

Prior audit/state/outer receipts and source hashes are pinned, and bounded
resource guards are retained. Author no-Lean preflight exited 0. Runner
SHA-256:
`0424a9636c79f6aa0e3b513fa6da8c9f616e932bf3abf52f1e60f3f3e08d55ab`;
manifest SHA-256:
`ce7dfb6b550b76c2e9871261bf889e64144c0058354a6f683252f7aba806c7ad`;
new source SHA-256:
`c4a4d8cf60b72bc32475d5aa8a9549a05e3cf567fe4c33b983ad11133b6acaa9`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-beta-byte-probe-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-beta-byte-probe-failure-independent/README.md) passed; the packet is frozen.
