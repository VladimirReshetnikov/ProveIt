# Sign20 port-dependent square coefficients: failed cast retry

Author-observed outer session `6576` exited 1. The first three stages passed,
but the fourth again failed both proofs: after rewriting C to integer casts,
casts of compound integer polynomials remained undistributed. Both reports
include `sorryAx`; no coefficient object or postflight is claimed. The [independent failure audit](../../../reviews/nine-sharing-sign20-leading-coeff-retry-failure-independent/README.md) passed; the packet is frozen.
