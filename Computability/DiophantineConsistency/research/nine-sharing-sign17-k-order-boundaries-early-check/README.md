# K early cross-block order boundaries

This checked 23-stage attempt replays the independently audited Fin224
weight union in one context, then proves numeric and actual-weight
comparisons at candidate row boundaries 31/32 and 95/96. These close only two
cross-block comparisons; the Start/non-Start probe, other boundaries, full
ordering, actual ranks, K and file binding remain separate. Usual per-child
guards apply. Author no-Lean preflight exited 0.

Runner SHA-256:
`196aca5e06bea409be381fc449c79117003459a3124439d9e2ab43ba275b20bc`;
manifest SHA-256:
`15dfd5a905dcc49f8bf09f7460beeb5e83bc35baf05d19fa681b704980121ee4`;
source SHA-256:
`476d6c8d539fa60edff8c66a9bdcc9cd4c0350ca36a9d6df6b03d9ff0ac6fbc3`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-order-boundaries-early-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-order-boundaries-early-terminal-independent/README.md) passed; the packet is frozen.
