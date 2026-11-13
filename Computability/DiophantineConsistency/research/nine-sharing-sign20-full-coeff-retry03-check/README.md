# Sign20 full coefficient explicit count-cons retry

Seven source-only stages propose the seed-axis coefficient `2*(p 0)^4` and
the Fin20 polynomial lower bound ≥20 assuming `p 0 ≠ 0`. The only source
changes add `List.count_cons` to the two failed finite-list simp proofs.
Guard/resource limits are retained. No lower result is claimed before Lean
and independent audit.

Author no-Lean preflight exited 0 for seven stages. Runner SHA-256:
`a592544ed5133152b0fb5513ec802a3c5585a74f1fedcbc18de6e08c935165a7`;
manifest SHA-256:
`eead673b80c68ee61f4f95fa2ac9f09777523bb2d68c8707c1511efb473a215e`.
The [independent prelaunch audit](../../reviews/nine-sharing-sign20-full-coeff-retry03-prelaunch-independent/README.md) passed. Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign20-full-coeff-retry03-failure-independent/README.md) passed; the packet is frozen.
