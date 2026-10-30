# Package-only graph audit with companions

This audit-only run resolved 725 current project-source modules, 93 direct external package objects and 279 available direct package companion artifacts. `Init.olean.server` is present in the package-only mirror, and project namespaces are excluded. The exact source hashes, package-object/companion hashes, compiler and Lake anchors are recorded in `state.json`; transitive package source/object provenance remains inherited. No source module was compiled and this is not a proof build or independent replay.
