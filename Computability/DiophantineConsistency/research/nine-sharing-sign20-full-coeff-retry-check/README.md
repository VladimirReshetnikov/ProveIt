# Sign20 full coefficient structural-distinctness retry

Seven source-only stages propose seed-axis coefficient `2*(p 0)^4` and the
Fin20 polynomial lower bound ≥20 assuming `p 0 ≠ 0`. The sole source change
from the failed first attempt replaces free-port `decide` with constructor
discrimination; all statements remain unchanged. Guard/resource limits
are retained. No lower result is claimed before Lean and independent audit.

Author no-Lean preflight exited 0 for seven stages. Runner SHA-256:
`3b1ffd722a9693985ab306c5913f004201b146368a602d05d257a9da3cb0e6f4`;
manifest SHA-256:
`61618db0058b2623b6c1bc52254e77186253f08b81780a2393d261b595de982c`.
The [independent prelaunch audit](../../reviews/nine-sharing-sign20-full-coeff-retry-prelaunch-independent/README.md) passed. Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign20-full-coeff-retry-failure-independent/README.md) passed; the packet is frozen.
