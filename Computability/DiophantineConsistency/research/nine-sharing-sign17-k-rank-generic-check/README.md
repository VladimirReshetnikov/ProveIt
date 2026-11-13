# Generic finite candidate-rank criterion

This source-only proposal avoids the unavailable physical permutation module.
It asks Lean to prove a criterion for arbitrary `rank`, candidate `f`, and
`weight` functions on `Fin 942`. Its explicit hypotheses require the rank
map to preserve zero, be injective, and order nonzero indices in reverse
weight order; the candidate must preserve zero, send nonzero to nonzero, and
have strictly descending weights on its nonzero positions. The proposed
conclusion is `rank (f i) = i` for every position. It is a generic ingredient:
no actual physical map specialization, candidate hypotheses, complete K,
file binding, or consistency equivalence follows by itself.

The previous [physical-map attempt](../nine-sharing-sign17-k-rank-certificate-check/README.md) failed because that module was not imported. This proposal retains
the source-pinned `Mathlib.Order.WellFounded` import, which reached source
elaboration in that failed attempt. The unchanged per-child resource limits
apply. Author no-Lean preflight exited 0 for 16 stages. Runner SHA-256:
`153f72c324055edc68bf95495ebe32fc060db164fa0e8b7af3b86063e068add0`;
manifest SHA-256:
`81bc5f1a17d6d438e8f1f5fd29e517963b12be8be6857366ef24919859ae1eae`;
source SHA-256:
`cea219c97d9f7aa730f80d7682d3ed39552a6294a133143f810f1f9c1f23694f`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-rank-generic-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-rank-generic-terminal-independent/README.md) passed; the packet is frozen.
