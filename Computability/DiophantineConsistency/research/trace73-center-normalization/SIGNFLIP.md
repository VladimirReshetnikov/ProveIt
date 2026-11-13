# An all-ring carrier-sign flip for the actual trace75 graph

`Trace75SignFlip.Z_move` proves for arbitrary commutative rings, ring-valued
ports and valuations, that adding `2*d` to slot 7 changes the actual trace75
carrier `Z` by `2*M*d` and keeps the other output-relevant registers `Q`,
`M`, `Gn` and `V` unchanged.
`value_flip` consequently proves that, if the original carrier is `-M*d`,
the update preserves the actual trace75 output. Both are all-ring Lean
statements about `TenPositiveTrace75.value75`; they do not by themselves
produce a positive model witness or prove a positive trace73 center.

The guarded author run `observations/flip-attempt02/` and tool session 59862
exited 0; the reported axiom list is `[propext, Quot.sound]`. The object
`/tmp/trace75-signflip-5t6uw3qf/Trace75SignFlip.olean` has SHA-256
`853d9841662ae9ae17388da47c4cc684332e99cbdc3346035564c4997ade70af`.
The source, runner and terminal hashes are
`f317cefbd6b42729506548a0936cfa4073fcf8819508822c2c4b87dca2b70d5d`,
`ac6961af19320252589ac0112c18cd388289a1e92ce161fe9037acab185af636`, and
`6ac4b60f6a0efa1a417f8ce02dd90271759e1bd155d3a7e7883e745de4ea827a`.
Attempt01 failed because the unchanged register projections were not reduced
by a proposed `change`; its source and diagnostic are retained. The direct
fresh trace75 graph provider is pinned, while full package/transitive/dynamic
ancestry and independent replay remain outside this check.
