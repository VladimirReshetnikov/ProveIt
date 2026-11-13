# Sign17 corrected-axis split binding: associativity retry

This fresh-output attempt retains seven stages and all source statements. Its
only Lean-source change replaces the failed final `rfl` with explicit reverse
multiplication associativity. Earlier stages are replayed, rather than relying
on successful children of the failed parent. The [first split attempt](../nine-sharing-sign17-axis-root-binding-staged-check/attempt01/README.md)
remains recorded; guards and resource limits are unchanged. No new checked
binding theorem or polynomial lower bound is claimed yet.

Author no-Lean preflight exited 0. Runner SHA-256:
`37cd015542436fa25edbce2a6b70736e0ea195a9453c7f4ac046fd84d7bd11df`;
manifest SHA-256:
`70fa83ff687e0a3ed3bd3f1a044e7d3b83249e7a79c0239981536b6766edaa08`;
new source SHA-256:
`be5fc13083f7c929bd189304b4b78a124fd47317bc9981bbc86b1590d54b67d0`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-axis-root-binding-staged-retry-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-axis-root-binding-staged-retry-terminal-independent/README.md) passed; the packet is frozen.
