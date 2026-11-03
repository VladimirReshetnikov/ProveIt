# Scaled strong seed above any internal bound

`TenPositiveScaledStrongSeedAbove.strong_seed_above` constructs the same
scaled strong-Pell data as the unbounded seed, with the additional guarantee
that its internal index m exceeds an arbitrary supplied internal L. In every
IΣ₁ model and for positive c,τ it produces positive i,f and m>L with
`ycoord(m,a)=(i*c²)*τ`, the strong norm for f, and exact doubled coordinates.
This is intended to give room for later positive carrier coordinates; it does
not itself construct the auxiliary Pell/transport witnesses, zero a graph,
prove halt equivalence, or establish internal iPRA derivability.

Accepted guarded check `observations/strongabove-attempt01/` produced
`/tmp/scaled-strong-seed-above-xth2jyyo/ScaledStrongSeedAbove.olean`, SHA-256
`f08d5ae2398a195e429a742bd62dea1d51cbb6624b070ea8ad3d5cb3a5a33577`.
Both source-direct imports are resolved and checked against explicit selected
paths and hashes before and after Lean. Broader transitive source-object,
project/package and dynamic-library coverage is inherited.
