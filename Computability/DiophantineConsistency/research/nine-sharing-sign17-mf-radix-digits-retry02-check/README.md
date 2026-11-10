# MF radix digits: explicit high-digit cons identity retry

This fresh-output sixteen-stage attempt retains the theorem statements and
all provider sources. The sole proof change replaces a recursion-prone
first-digit reduction with a separately proved identity `highDigits = 4 ::
tailDigits`, then rewrites the decoder using that identity. The [previous
failure](../nine-sharing-sign17-mf-radix-digits-retry-check/attempt01/README.md)
remains recorded. Resource limits remain unchanged; no new theorem, raw byte,
gzip or JSON binding is claimed before checking.

Author no-Lean preflight exited 0. Runner SHA-256:
`b1b61f81bcecdec39d399796a502b242cea50ede4bbe288de191ce364d317f26`;
manifest SHA-256:
`ea8035da0bdc45c41fa4d736b20b6354696f9f04459df9bc55920f34159f763b`;
new source SHA-256:
`375a19a150c5ceefd186847bfacae12639c35512c5c9327e9de4618dade2b8b0`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mf-radix-digits-retry02-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-mf-radix-digits-retry02-terminal-independent/README.md) passed; the packet is frozen.
