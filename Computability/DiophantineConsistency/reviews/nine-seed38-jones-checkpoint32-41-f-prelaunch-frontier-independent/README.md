# Independent prelaunch review: F checkpoint

Pass, source and point-provider scope only; no Lean replay. The d32 node computes `(A²−1)E²+1`; the proposed value substitutes the checked A and E expressions, and the two-step d32→d34 path composes with the existing d34→d41 lookup. The checker checks exact finite-index chains, source statement agreement at d32/d41, source and runner pins, and a successful guarded no-Lean preflight.

Elaboration and resource fit remain untested. The statement is a symbolic local F result with d11 rank opaque, not a full output identity or external JSON binding. Provider guards are point-in-time and do not establish a complete transitive trace; inherited numeric outer-exit limitation remains.

Checker SHA-256 `4c7a44dae2f98521b9d7c3d42f735af8254e6996a2b81f8281d10e86fd91992a`; result SHA-256 `2cf254aed868e51c21c0e20a76874f8ccf54daab92655fdddc07899e99385e52`.
