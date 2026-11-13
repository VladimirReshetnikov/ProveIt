# Sign24 full coefficient constant-evaluation retry

The prior run checked the whole seed's axis eighth coefficient as one, but
the direct-expression lower-bound module left the generic diagonal
evaluation's integer-constant case unresolved. This source-only retry adds
the standard fact that the `MvPolynomial.eval₂Hom` ring homomorphism preserves
integer casts. Its other six source modules and proposed final statement are
unchanged. The earlier seed theorem's unused simp warning is intentionally
retained. The guard limits are unchanged; elaboration is untested. Independent
prelaunch review and an assigned Lean slot are required.

The proposed result is a degree lower bound, not yet the exact-degree equality
or JSON/port-byte/PDF correspondence.
