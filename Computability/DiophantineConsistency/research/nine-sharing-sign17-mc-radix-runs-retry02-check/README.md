# Sign17 MC symbolic radix runs: redundant-tactic retry

This fresh-output seventeen-stage attempt retains all statements and replays
the generic digit core. Its sole Lean-source change removes `decide` after a
length simplification already closed that goal. The [previous partial failure](../nine-sharing-sign17-mc-radix-runs-retry-check/attempt01/README.md)
remains recorded; it had a successful core child but a failed outer attempt.
The core is replayed, not assumed from that failed parent. Resource guards
are unchanged. No new radix-run or byte/file theorem is claimed yet.

Author no-Lean preflight exited 0. Runner SHA-256:
`cec8beb3d2f9e6f436cc9ab3e3e41e1430e145b0d91cb1349e9decaf5b292e0f`;
manifest SHA-256:
`85752488724fbf6ba62a515c100d7fbf8c7715214508f4ad1444b934f05eb7b9`;
new source SHA-256:
`6893f9d6e22ec2d7d39d9167d105fdebe3ccc49c202f8d99008ed9c745d26875`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mc-radix-runs-retry02-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-mc-radix-runs-retry02-terminal-independent/README.md) passed; the packet is frozen.
