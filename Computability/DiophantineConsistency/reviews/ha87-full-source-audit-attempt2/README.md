# Full-source graph and package-mirror audit

This audit-only run resolved 725 current project-source modules and 93 directly imported external package objects. Its package-only mirror excludes project namespaces; its graph, source hashes, selected direct external-object hashes and compiler/Lake anchors are recorded in `state.json`. Package objects' transitive source/object provenance remains inherited. The run compiled no modules and is not an HA proof build or an independent replay. Source hashes must be refreshed if the workspace changes before the full build.
