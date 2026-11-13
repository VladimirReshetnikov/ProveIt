# Guarded positive-zero equivalence

`TenPositive79Forward.positive_zero_iff_guarded` proves in every supported
IΣ₁ model, for arbitrary natural ports with positive beta, that the old 80-row
positive-zero existence is equivalent to 79-row positive-zero existence with
the explicit condition `F+C<q`. The old-to-new direction obtains positivity
of `C=q−F−alpha` from the checked old-graph transport/mask theorem, proves the
new guard using the old positive alpha, and uses the involutive coordinate
map. The opposite direction is the separately checked `guarded_to_old`.

This is **not** an unguarded 79-row equivalence: nothing in this packet proves
`F+C<q` from an arbitrary positive new-graph zero. It does not establish an
iPRA proof for the unguarded 79 equation or a file-binding theorem. The
ring-to-candidate JSON comparison remains external.

The accepted guarded author run is `observations/forward-attempt02/`, which
produced `/tmp/mask79-forward-g_hxzbm9/Mask79Forward.olean`, SHA-256
`3469bbdc3d8c50c22b06dd5a5ce01bd8f72c2aa392f9cadb0fd8b3f5080fdd0a`.
It reports the Lean metatheory axioms `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`. Attempt01 failed on a namespace collision
and is retained. Source and runner hashes are respectively
`2153aa2a0147169a5d32991fc4397daa05705dde48858637a3f522c140ffe95d` and
`a9da84ef89b3b00b2a2bf1cbfc62aadd3eea5f86f642159d00fbc6bf3dd06556`.
The direct import is pinned; the earlier project-transitive, historical
source/object, package and dynamic limitations are inherited.
