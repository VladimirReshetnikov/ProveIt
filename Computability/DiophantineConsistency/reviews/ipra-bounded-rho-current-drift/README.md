# Scoped source drift in the companion-pinned literal proof

The companion-pinned literal proof is a fixed historical-provider result. Its selected `IPRABoundedErasure.olean` and `IPRABoundedMappedErasure.olean` exactly match their independently recorded earlier author objects, while the corresponding current workspace source hashes differ from those author source snapshots. The source/object SHA-256 pairs and match flags are recorded in `audit.json`.

For merge `b75c4ba7a1`, the first-parent `IPRABoundedErasure.lean` SHA-256 was `256b2116a45ddb5b63e20ef5f0bd354a26576a65e0dc635ab7ad301cf582101a`, equal to the earlier selected object's recorded source snapshot. The merge's source SHA-256 is `be1180092f9f166d613bbab35a754b32727a09360e03c5025b2a416c80de11c7`, which matches the workspace at this post-merge audit. Our earlier live workspace observation already saw the latter value, so it was not a reliable pre-merge reading; the first-parent Git blob supplies the pre-merge hash.

These observations do not invalidate the frozen proof snapshot and do not by themselves imply a semantic difference. They do rule out treating this particular replay as proof of a complete current-source ancestry. A separately guarded source-directed rebuild is needed for that stronger claim.
