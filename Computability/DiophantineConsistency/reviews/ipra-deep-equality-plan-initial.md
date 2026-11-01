# Initial deep/equality planning attempt

The initial planning run stopped before creating any provider or compiling a module because its guessed count was 35 while its unrestricted current-source traversal reported 36. The extra node was `PRARewritingWitnessBound`, reached only by descending through a current source corresponding to an already-selected inherited historical object. The source/object ancestry there was not authenticated by the parent, so treating that path as a current build dependency would conflate source and object graphs. The initial frozen source snapshot is `/tmp/ipra-deep-equality-rebase-ibbx3hbt`; no PASS state was produced.

The corrected planner stops its current-source traversal at explicit, rehashed inherited-object boundaries, snapshots only the sources it actually rebuilds, and retains the parent and other package ancestry as historical. This limits rather than upgrades the provenance claim.
