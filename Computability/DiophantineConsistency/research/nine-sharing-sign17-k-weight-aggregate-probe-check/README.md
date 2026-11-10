# K tile-weight aggregation feasibility probe

This bounded sixteen-stage source-only attempt proposes a single universally
quantified theorem for 32 actual Lean tile-weight equalities, using two finite
vectors of candidate indices and weights. Its `fin_cases`/`decide +kernel`
proof checks each finite case from the actual definitions. The guard verifies
both vectors against independently audited external witness rows 0–31 and
pins the audited four-case feasibility sample. This experiment rechecks the
first 32 rows; it does not import or aggregate the existing batch00 object.

If viable, the same pattern could turn each future batch into one usable
finite-table theorem instead of dozens of separate declarations. It does not
prove actual physical ranks, other rows, full K, or external file/gzip binding.
Resource caps are unchanged from the individual 32-row batch. Author no-Lean
preflight exited 0. Runner SHA-256:
`fcd7a2f5aa89ce666ab21ffea1a29c569aa9c71f6347a60db6d932f0cc7790b5`;
manifest SHA-256:
`ab901933f9cd0cdf216ad1ded111f9ee9e88fa10a031851d25ac3e8bff523b7f`;
new source SHA-256:
`240f1f6909e9363022541fa479ef31025402e2a2faaa616359658e9d014f81f9`;
generator SHA-256:
`1281e0551fe3b0f3f39d5290388ce75ec450a4672d75e8b8021df1ef73315d21`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-weight-aggregate-probe-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-weight-aggregate-probe-terminal-independent/README.md) passed; the packet is frozen.
