# Sign20 full coefficient symbolic-count retry

Seven source-only stages propose the seed-axis coefficient `2*(p 0)^4` and
the Fin20 polynomial lower bound ≥20 assuming `p 0 ≠ 0`. The only source
changes replace failed definitional count reductions with finite-list
simplification. Guard/resource limits are retained. No lower result is claimed
before Lean and independent audit.

Author no-Lean preflight exited 0 for seven stages. Runner SHA-256:
`3748a6ea85d6c5c9cc63232fe62f2ea33678d9aa70e4d8b3e6103334a8056ca4`;
manifest SHA-256:
`797289e257dede4b0fe3eaa1d9d6342a21b258e9b1eecbdac3b1e77455fb43fd`.
The [independent prelaunch audit](../../reviews/nine-sharing-sign20-full-coeff-retry02-prelaunch-independent/README.md) passed. Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign20-full-coeff-retry02-failure-independent/README.md) passed; the packet is frozen.
