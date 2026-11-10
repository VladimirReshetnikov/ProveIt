# Sign17 symbolic MF source-port radix digits

This sixteen-stage source-only attempt replays the audited symbolic provider
and proposes a compact 2012-digit base-`2^47` representation for the exact
current source high-mask port, `highPort + beta = CurrentWindowCarry2011.ports 3`.
It replaces the first high-mask digit 4 by 3, retains the remaining 2010
digits, and appends a most-significant 1 to account for beta. The proof avoids
a whole 94,518-bit kernel computation, using the digit-append identity and
symbolic arithmetic instead.

No checked new theorem is claimed yet. Byte chunks, whole byte-list decoding,
external raw/gzip/JSON binding and the other remaining port are separate.
The unchanged resource guards are retained. Author no-Lean preflight exited 0.
Runner SHA-256:
`f8f126fbdc16d8e5bbfd44b6febe05d15b3d04f5651ccef24697a55391702462`;
manifest SHA-256:
`d468b6d74fa882fce0439f5c417a62bec5a00791d9af5ca0f34e339eff37f0fc`;
new source SHA-256:
`6e3b6ec8a16a91be1c0b66f5c1bb2c838d71e2a62ebd662a6c3075b50217da2d`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mf-radix-digits-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-mf-radix-digits-terminal-independent/README.md) passed; the packet is frozen.
